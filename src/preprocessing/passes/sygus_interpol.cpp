/*********************                                                        */
/*! \file sygus_interpol.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds and Yoni Zohar
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Sygus interpolation preprocessing pass, which transforms an arbitrary
 ** input into an interpolation problem. Heavily based on sygus_abduct.cpp
 **/

#include "preprocessing/passes/sygus_interpol.h"

#include "expr/node_algorithm.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "smt/smt_statistics_registry.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/quantifiers_rewriter.h"
#include "theory/quantifiers/term_util.h"
#include "theory/rewriter.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace preprocessing {
namespace passes {

SygusInterpol::SygusInterpol(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "sygus-interpol"){};

PreprocessingPassResult SygusInterpol::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  NodeManager* nm = NodeManager::currentNM();
  Trace("sygus-interpol") << "Run sygus interpol..." << std::endl;

  Trace("sygus-interpol-debug") << "Collect symbols..." << std::endl;
  std::unordered_set<Node, NodeHashFunction> symsetAxioms;
  std::unordered_set<Node, NodeHashFunction> symsetConjecture;
  std::vector<Node>& asserts = assertionsToPreprocess->ref();
  // do we have any assumptions, e.g. via check-sat-assuming?
  bool usingAssumptions = (assertionsToPreprocess->getNumAssumptions() > 0);
  // The following is our set of "axioms". We construct this set only when the
  // usingAssumptions (above) is true. In this case, our input formula is
  // partitioned into Fa ^ Fc as described in the header of this class, where:
  // - The conjunction of assertions marked as assumptions are the negated
  // conjecture Fc. We save these assertions in negateConjectureList; and
  // - The conjunction of all other assertions are the axioms Fa.
  std::vector<Node> axioms;
  std::vector<Node> negatedConjectureList;
  for (size_t i = 0, size = asserts.size(); i < size; i++)
  {
    // if we are not an assumption, add it to the set of axioms
    if (usingAssumptions && i < assertionsToPreprocess->getAssumptionsStart())
    {
      expr::getSymbols(asserts[i], symsetAxioms);
      axioms.push_back(asserts[i]);
    } else {
      expr::getSymbols(asserts[i], symsetConjecture);
      negatedConjectureList.push_back(asserts[i]);
    }
  }
  std::unordered_set<Node, NodeHashFunction> symsetShared;
  for (const auto& elem: symsetConjecture) {
    if (symsetAxioms.find(elem) != symsetAxioms.end()) {
      symsetShared.insert(elem);
    }
  } 
  Trace("sygus-interpol-debug")
      << "...finish, got " << symsetShared.size() << " shared symbols." << std::endl;

  Trace("sygus-interpol-debug") << "Setup symbols..." << std::endl;
  std::vector<Node> syms;
  std::vector<Node> vars;
  std::vector<Node> varlist;
  std::vector<TypeNode> varlistTypes;
  for (const Node& s : symsetShared)
  {
    TypeNode tn = s.getType();
    if (tn.isFirstClass())
    {
      std::stringstream ss;
      ss << s;
      Node var = nm->mkBoundVar(tn);
      syms.push_back(s);
      vars.push_back(var);
      Node vlv = nm->mkBoundVar(ss.str(), tn);
      varlist.push_back(vlv);
      varlistTypes.push_back(tn);
    }
  }
  Trace("sygus-interpol-debug") << "...finish" << std::endl;

  Trace("sygus-interpol-debug") << "Make interpolation predicate..." << std::endl;
  // make the interpolation predicate to synthesize
  TypeNode interpolType = varlistTypes.empty() ? nm->booleanType()
                                          : nm->mkPredicateType(varlistTypes);
  Node interpol = nm->mkBoundVar("A", interpolType);
  Trace("sygus-interpol-debug") << "...finish" << std::endl;

  Trace("sygus-inteprol-debug") << "Make interpol predicate app..." << std::endl;
  std::vector<Node> achildren;
  achildren.push_back(interpol);
  achildren.insert(achildren.end(), vars.begin(), vars.end());
  Node interpolApp = vars.empty() ? interpol : nm->mkNode(APPLY_UF, achildren);
  Trace("sygus-interpol-debug") << "...finish" << std::endl;

  Trace("sygus-interpol-debug") << "Set attributes..." << std::endl;
  // set the sygus bound variable list
  Node abvl = nm->mkNode(BOUND_VAR_LIST, varlist);
  interpol.setAttribute(theory::SygusSynthFunVarListAttribute(), abvl);
  Trace("sygus-interpol-debug") << "...finish" << std::endl;

  Trace("sygus-interpol-debug") << "Make conjecture body..." << std::endl;
  Node Fa = asserts.size() == 1 ? asserts[0] : nm->mkNode(AND, asserts);
  Fa = Fa.substitute(syms.begin(), syms.end(), vars.begin(), vars.end());
  // Fa ( x ) => A ( x )
  Node firstImplication = nm->mkNode(IMPLIES, Fa, interpolApp);
  Trace("sygus-interpol-debug") << "...finish" << std::endl;

  Trace("sygus-interpol-debug") << "Make conjecture..." << std::endl;
  Node Fc = nm->mkNode(AND, negatedConjectureList);
  Node negFc = nm->mkNode(NOT, Fc);
  Node secondImplication = nm->mkNode(IMPLIES, interpolApp, negFc);

  Node constraint = nm->mkNode(AND, firstImplication, secondImplication);
  constraint = theory::Rewriter::rewrite(constraint);

  Node fbvl = nm->mkNode(BOUND_VAR_LIST, interpol);

  // forall A. exists x. ~( A( x ) => ~input( x ) )
  Node res = constraint.negate();
  Node bvl = nm->mkNode(BOUND_VAR_LIST, vars);
  res = nm->mkNode(EXISTS, bvl, res);
  res = nm->mkNode(FORALL, fbvl, res);
  Trace("sygus-interpol-debug") << "...finish" << std::endl;

  res = theory::Rewriter::rewrite(res);

  Trace("sygus-interpol") << "Generate: " << res << std::endl;

  Node trueNode = nm->mkConst(true);

  assertionsToPreprocess->replace(0, res);
  for (size_t i = 1, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    assertionsToPreprocess->replace(i, trueNode);
  }

  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
