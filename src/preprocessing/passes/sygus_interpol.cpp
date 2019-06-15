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
#include "theory/quantifiers/sygus/sygus_grammar_cons.h"
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
  //symbols that occur in the axioms
  std::unordered_set<Node, NodeHashFunction> symsetAxioms;
  //symbols that occur in the conjecture
  std::unordered_set<Node, NodeHashFunction> symsetConjecture;
  //symbols that occur either in the axioms or in the conjecture
  std::unordered_set<Node, NodeHashFunction> symsetAll;
  //symbols that occur both in the axioms and the conjecture
  std::unordered_set<Node, NodeHashFunction> symsetShared;
  //symbols that occur in exactly one of the axioms or the conjecture
  std::unordered_set<Node, NodeHashFunction> symsetNotShared;
  //all assertions (axioms and conjecture)
  std::vector<Node>& asserts = assertionsToPreprocess->ref();
  // do we have any assumptions, e.g. via check-sat-assuming?
  bool usingAssumptions = (assertionsToPreprocess->getNumAssumptions() > 0);
  Assert(usingAssumptions);
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
    // if we are not an assumption, add it to the set of axioms and its symbols to the set of axiom symbols
    if (i < assertionsToPreprocess->getAssumptionsStart())
    {
      expr::getSymbols(asserts[i], symsetAxioms);
      axioms.push_back(asserts[i]);
      Trace("sygus-interpol-debug") << "assertion " << asserts[i].toString() << " is an assumption" << std::endl;
    // otherwise, add it to the set of conjectures and its symbols to the set of conjecture symbols
    } else {
      expr::getSymbols(asserts[i], symsetConjecture);
      negatedConjectureList.push_back(asserts[i]);
      Trace("sygus-interpol-debug") << "assertion " << asserts[i].toString() << " is a negated conjecture" << std::endl;
    }
    //Either way, add the symbols to the set of all symbols
    expr::getSymbols(asserts[i], symsetAll);
  }
  //compute the set of shared symbols and the set of not shared symbols
  for (const auto& elem: symsetConjecture) {
    if (symsetAxioms.find(elem) != symsetAxioms.end()) {
      Trace("sygus-interpol-debug") << "symbol " << elem.toString() << " is shared" << std::endl;
      symsetShared.insert(elem);
    } else {
      Trace("sygus-interpol-debug") << "symbol " << elem.toString() << " is not shared" << std::endl;
      symsetNotShared.insert(elem);
    }
  } 
  for (const auto& elem: symsetAxioms) {
    if (symsetAxioms.find(elem) == symsetAxioms.end()) {
      symsetNotShared.insert(elem);
    }
  } 

  Trace("sygus-interpol-debug")
      << "...finish, got " << symsetShared.size() << " shared symbols." << std::endl;

  Trace("sygus-interpol-debug") << "Setup symbols..." << std::endl;
  //containers for variables that occur as parameters to the synthesized function
  std::vector<Node> syms;
  std::vector<Node> vars;
  std::vector<Node> sharedVars;
  std::vector<Node> varlist;
  std::vector<Node> varlistShared;
  std::vector<TypeNode> varlistTypes;
  std::vector<TypeNode> varlistTypesShared;
  //containers for variables that may occur in the body of the synthesized function
  std::unordered_set<Node, NodeHashFunction> nonSharedVarSet;
  for (const Node& s : symsetAll)
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
      Trace("sygus-interpol-debug") << "s = " << s.toString() << " vlv = " << vlv.toString() << std::endl;
      varlist.push_back(vlv);
      varlistTypes.push_back(tn);
      if (symsetShared.find(s) == symsetShared.end()) {
         Trace("sygus-interpol-debug") << "symbol " << s.toString() << " of type  " << tn.toString() <<  " added to non shared" << std::endl;
         nonSharedVarSet.insert(vlv);
      } else {
         varlistShared.push_back(vlv);
         varlistTypesShared.push_back(tn);
         sharedVars.push_back(var);
         Trace("sygus-interpol-debug") << "symbol " << s.toString() << " of type  " << tn.toString() <<  " added to shared" << std::endl;
      }
    }
  }

  Trace("sygus-interpol-debug") << "...finish" << std::endl;

  Trace("sygus-interpol-debug") << "Make interpolation predicate..." << std::endl;
  // make the interpolation predicate to synthesize
  TypeNode interpolType = varlistTypesShared.empty() ? nm->booleanType()
                                          : nm->mkPredicateType(varlistTypesShared);
  Node interpol = nm->mkBoundVar("A", interpolType);
  Trace("sygus-interpol-debug") << "...finish" << std::endl;

  // set the sygus bound variable list
  Node abvl = nm->mkNode(BOUND_VAR_LIST, varlist);
  Node abvlShared = nm->mkNode(BOUND_VAR_LIST, varlistShared);
  d_preprocContext->getSmt()->setInterpolationVars(varlistShared);
  
  Trace("sygus-interpol-debug")
        << "Make sygus grammar attribute..." << std::endl;
  std::map<TypeNode, std::vector<Node> > extra_cons;
  std::map<TypeNode, std::vector<Node> > exclude_cons;
  std::unordered_set<Node, NodeHashFunction> terms_irrelevant;
  TypeNode interpolGTypeS = CVC4::theory::quantifiers::CegGrammarConstructor::mkSygusDefaultType(
    nm->booleanType(),
    abvlShared,
    "interpolation_grammar",
    extra_cons,
    exclude_cons,
    terms_irrelevant,
    d_preprocContext->getSmt()->getLogicInfo().isLinear()
      );
  Node sym = nm->mkBoundVar("sfproxy_interpol", interpolGTypeS);
  std::vector<Expr> attrValue;
  attrValue.push_back(sym.toExpr());
  d_preprocContext->getSmt()->setUserAttribute(
        "sygus-synth-grammar", interpol.toExpr(), attrValue, "");
  Trace("sygus-interpol-debug") << "Finished setting up grammar." << std::endl;
  


  Trace("sygus-inteprol-debug") << "Make interpol predicate app..." << std::endl;
  std::vector<Node> achildren;
  achildren.push_back(interpol);
  achildren.insert(achildren.end(), sharedVars.begin(), sharedVars.end());
  Node interpolApp = sharedVars.empty() ? interpol : nm->mkNode(APPLY_UF, achildren);
  Trace("sygus-interpol-debug") << "...finish" << std::endl;

  Trace("sygus-interpol-debug") << "Set attributes..." << std::endl;
  interpol.setAttribute(theory::SygusSynthFunVarListAttribute(), abvlShared);
  Trace("sygus-interpol-debug") << "...finish" << std::endl;

  Trace("sygus-interpol-debug") << "Make conjecture body..." << std::endl;
  Node Fa = axioms.size() == 1 ? axioms[0] : nm->mkNode(AND, axioms);
  Fa = Fa.substitute(syms.begin(), syms.end(), vars.begin(), vars.end());
  // Fa ( x ) => A ( x )
  Node firstImplication = nm->mkNode(IMPLIES, Fa, interpolApp);
  Trace("sygus-interpol-debug") << "...finish" << std::endl;

  Trace("sygus-interpol-debug") << "Make conjecture..." << std::endl;
  Node Fc = nm->mkNode(AND, negatedConjectureList);
  Fc = Fc.substitute(syms.begin(), syms.end(), vars.begin(), vars.end());
  Node negFc = nm->mkNode(NOT, Fc);
  Node secondImplication = nm->mkNode(IMPLIES, interpolApp, negFc);

  Node constraint = nm->mkNode(AND, firstImplication, secondImplication);
  constraint = theory::Rewriter::rewrite(constraint);

  Node fbvl = nm->mkNode(BOUND_VAR_LIST, interpol);

    // sygus attribute
  Node sygusVar = nm->mkSkolem("sygus", nm->booleanType());
  theory::SygusAttribute ca;
  sygusVar.setAttribute(ca, true);
  Node instAttr = nm->mkNode(INST_ATTRIBUTE, sygusVar);
  std::vector<Node> iplc;
  iplc.push_back(instAttr);
  Node instAttrList = nm->mkNode(INST_PATTERN_LIST, iplc);
  
  // forall A. exists x. ~( A( x ) => ~input( x ) )
  Node res = constraint.negate();
  Node bvl = nm->mkNode(BOUND_VAR_LIST, vars);
  res = nm->mkNode(EXISTS, bvl, res);
  res = nm->mkNode(FORALL, fbvl, res, instAttrList);
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
