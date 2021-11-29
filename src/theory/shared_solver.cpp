/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The shared solver base class.
 */

#include "theory/shared_solver.h"

#include "expr/node_visitor.h"
#include "options/datatypes_options.h"
#include "options/smt_options.h"
#include "theory/ee_setup_info.h"
#include "theory/logic_info.h"
#include "theory/theory_engine.h"
#include "theory/theory_inference_manager.h"

namespace cvc5 {
namespace theory {

// Always creates shared terms database. In all cases, shared terms
// database is used as a way of tracking which calls to Theory::addSharedTerm
// we need to make in preNotifySharedFact.
// In distributed equality engine management, shared terms database also
// maintains an equality engine. In central equality engine management,
// it does not.
SharedSolver::SharedSolver(Env& env, TheoryEngine& te)
    : EnvObj(env),
      d_te(te),
      d_logicInfo(logicInfo()),
      d_sharedTerms(env, &d_te),
      d_preRegistrationVisitor(env, &te),
      d_sharedTermsVisitor(env, &te, d_sharedTerms),
      d_im(te.theoryOf(THEORY_BUILTIN)->getInferenceManager()),
      d_keep(context())
{
  d_valuation = new Valuation(&d_te);
}

SharedSolver::~SharedSolver() { delete d_valuation; }

bool SharedSolver::needsEqualityEngine(theory::EeSetupInfo& esi)
{
  return false;
}

void SharedSolver::preRegister(TNode atom)
{
  Trace("theory") << "SharedSolver::preRegister atom " << atom << std::endl;
  // This method uses two different implementations for preregistering terms,
  // which depends on whether sharing is enabled.
  // If sharing is disabled, we use PreRegisterVisitor, which keeps a global
  // SAT-context dependent cache of terms visited.
  // If sharing is disabled, we use SharedTermsVisitor which does *not* keep a
  // global cache. This is because shared terms must be associated with the
  // given atom, and thus it must traverse the set of subterms in each atom.
  // See term_registration_visitor.h for more details.
  if (d_logicInfo.isSharingEnabled())
  {
    // Collect the shared terms in atom, as well as calling preregister on the
    // appropriate theories in atom.
    // This calls Theory::preRegisterTerm and Theory::addSharedTerm, possibly
    // multiple times.
    NodeVisitor<SharedTermsVisitor>::run(d_sharedTermsVisitor, atom);
    // Register it with the shared terms database if sharing is enabled.
    // Notice that this must come *after* the above call, since we must ensure
    // that all subterms of atom have already been added to the central
    // equality engine before atom is added. This avoids spurious notifications
    // from the equality engine.
    preRegisterSharedInternal(atom);
    // additionally, directly add auxiliary shared terms
    // specified by the theory.
    std::vector<Node> sharedTerms;
    Theory* theory = d_te.theoryOf(atom);
    theory->getAuxiliarySharedTerms(atom, sharedTerms);
    for (Node n : sharedTerms)
    {
      Assert(!n.getType().isBoolean()
             || n.getKind() == kind::BOOLEAN_TERM_VARIABLE);
      Trace("polite-optimization")
          << "preRegisterShared: really adding shared term: " << n << std::endl;
      Trace("polite-optimization")
          << "preRegisterShared: the shared term was added via atom: " << atom
          << std::endl;
      TheoryIdSet theories = 0;
      theories = TheoryIdSetUtil::setInsert(Theory::theoryOf(atom), theories);
      theories = TheoryIdSetUtil::setInsert(Theory::theoryOf(n), theories);
      theories =
          TheoryIdSetUtil::setInsert(Theory::theoryOf(n.getType()), theories);
      Trace("polite-optimization")
          << "preRegisterShared: theories: "
          << TheoryIdSetUtil::setToString(theories) << std::endl;
      d_keep.insert(n);
      d_sharedTerms.addSharedTerm(atom, n, theories);

      if (n.getKind() == kind::BOOLEAN_TERM_VARIABLE)
      {
        // add a lemma about the Boolean variable
        NodeManager* nm = NodeManager::currentNM();
        Node pos = n;
        Node neg = nm->mkNode(kind::NOT, n);
        Node lemma = nm->mkNode(kind::OR, pos, neg);
        sendLemma(TrustNode::mkTrustLemma(lemma));
      }
    }
  }
  else
  {
    // just use the normal preregister visitor, which calls
    // Theory::preRegisterTerm possibly multiple times.
    NodeVisitor<PreRegisterVisitor>::run(d_preRegistrationVisitor, atom);
  }
  Trace("theory") << "SharedSolver::preRegister atom finished" << std::endl;
}

void SharedSolver::preNotifySharedFact(TNode atom)
{
  if (d_sharedTerms.hasSharedTerms(atom))
  {
    // Always notify the theories of the shared terms, which is independent of
    // the architecture currently.
    SharedTermsDatabase::shared_terms_iterator it = d_sharedTerms.begin(atom);
    SharedTermsDatabase::shared_terms_iterator it_end = d_sharedTerms.end(atom);
    for (; it != it_end; ++it)
    {
      TNode term = *it;
      TheoryIdSet theories = d_sharedTerms.getTheoriesToNotify(atom, term);
      for (TheoryId id = THEORY_FIRST; id != THEORY_LAST; ++id)
      {
        if (TheoryIdSetUtil::setContains(id, theories))
        {
          Theory* t = d_te.theoryOf(id);
          // call the add shared term method
          t->addSharedTerm(term);
        }
      }
      d_sharedTerms.markNotified(term, theories);
    }
  }
}

EqualityStatus SharedSolver::getEqualityStatus(TNode a, TNode b)
{
  return EQUALITY_UNKNOWN;
}

bool SharedSolver::propagateLit(TNode predicate, bool value)
{
  if (value)
  {
    return d_im->propagateLit(predicate);
  }
  return d_im->propagateLit(predicate.notNode());
}

bool SharedSolver::propagateSharedEquality(theory::TheoryId theory,
                                           TNode a,
                                           TNode b,
                                           bool value)
{
  // Propagate equality between shared terms to the one who asked for it
  Node equality = a.eqNode(b);
  if (value)
  {
    d_te.assertToTheory(equality, equality, theory, THEORY_BUILTIN);
  }
  else
  {
    d_te.assertToTheory(
        equality.notNode(), equality.notNode(), theory, THEORY_BUILTIN);
  }
  return true;
}

bool SharedSolver::isShared(TNode t) const { return d_sharedTerms.isShared(t); }

void SharedSolver::sendLemma(TrustNode trn, TheoryId atomsTo, InferenceId id)
{
  // Do we need to check atoms
  if (atomsTo != theory::THEORY_LAST)
  {
    d_te.ensureLemmaAtoms(trn.getNode(), atomsTo);
  }
  d_im->trustedLemma(trn, id);
}

void SharedSolver::sendConflict(TrustNode trn, InferenceId id)
{
  d_im->trustedConflict(trn, id);
}

}  // namespace theory
}  // namespace cvc5
