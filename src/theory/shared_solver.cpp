/*********************                                                        */
/*! \file shared_solver.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The shared solver base class
 **/

#include "theory/shared_solver.h"

#include "expr/node_visitor.h"
#include "options/datatypes_options.h"
#include "options/smt_options.h"
#include "theory/theory_engine.h"

namespace CVC4 {
namespace theory {

// Always creates shared terms database. In all cases, shared terms
// database is used as a way of tracking which calls to Theory::addSharedTerm
// we need to make in preNotifySharedFact.
// In distributed equality engine management, shared terms database also
// maintains an equality engine. In central equality engine management,
// it does not.
SharedSolver::SharedSolver(TheoryEngine& te, ProofNodeManager* pnm)
    : d_te(te),
      d_logicInfo(te.getLogicInfo()),
      d_sharedTerms(&d_te, d_te.getSatContext(), d_te.getUserContext(), pnm),
      d_preRegistrationVisitor(&te, d_te.getSatContext()),
      d_sharedTermsVisitor(&te, d_sharedTerms),
      d_keep(d_te.getUserContext())
{
  d_valuation = new Valuation(&d_te);
}

SharedSolver::~SharedSolver() {
  delete d_valuation;
}

bool SharedSolver::needsEqualityEngine(theory::EeSetupInfo& esi)
{
  return false;
}

void SharedSolver::preRegisterShared(TNode t)
{
  // register it with the equality engine manager if sharing is enabled
  if (d_logicInfo.isSharingEnabled())
  {
    preRegisterSharedInternal(t);
    NodeVisitor<SharedTermsVisitor>::run(d_sharedTermsVisitor, t);

    // additionally, directly add auxiliary shared terms
    // specified by the theory.
    std::vector<Node> sharedTerms;
    Theory* theory = d_te.theoryOf(t);
    theory->getAuxiliarySharedTerms(t, sharedTerms);
    for (Node n : sharedTerms)
    {
      Assert (!n.getType().isBoolean() || n.getKind()==kind::BOOLEAN_TERM_VARIABLE);
      Trace("polite-optimization")
          << "preRegisterShared: really adding shared term: " << n << std::endl;
      Trace("polite-optimization")
          << "preRegisterShared: the shared term was added via atom: " << t
          << std::endl;
      TheoryIdSet theories = 0;
      theories = TheoryIdSetUtil::setInsert(Theory::theoryOf(t), theories);
      theories = TheoryIdSetUtil::setInsert(Theory::theoryOf(n), theories);
      theories =
          TheoryIdSetUtil::setInsert(Theory::theoryOf(n.getType()), theories);
      Trace("polite-optimization")
          << "preRegisterShared: theories: "
          << TheoryIdSetUtil::setToString(theories) << std::endl;
      d_keep.insert(n);
      d_sharedTerms.addSharedTerm(t, n, theories);
      
      if (n.getKind() == kind::BOOLEAN_TERM_VARIABLE) {
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
    // just use the normal preregister visitor
    NodeVisitor<PreRegisterVisitor>::run(d_preRegistrationVisitor, t);
  }
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

void SharedSolver::sendLemma(TrustNode trn, TheoryId atomsTo)
{
  d_te.lemma(trn, LemmaProperty::NONE, atomsTo);
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

}  // namespace theory
}  // namespace CVC4
