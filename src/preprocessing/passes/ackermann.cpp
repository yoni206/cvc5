/*********************                                                        */
/*! \file ackermann.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz
 **   Yoni Zohar
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Ackermannization preprocessing pass.
 **
 **/

#include "preprocessing/passes/ackermann.h"

#include "smt_util/nary_builder.h"
#include "expr/node.h"

#include <unordered_set>

using namespace CVC4;
using namespace CVC4::theory;

namespace CVC4 {
namespace preprocessing {
namespace passes {

/* -------------------------------------------------------------------------- */

namespace
{

void storeFunction(
    TNode func,
    TNode term,
    FunctionToArgsMap& fun_to_args,
    SubstitutionMap& fun_to_skolem)
{
  if (fun_to_args.find(func) == fun_to_args.end())
  {
    fun_to_args.insert(make_pair(func, NodeSet()));
  }
  NodeSet& set = fun_to_args[func];
  if (set.find(term) == set.end())
  {
    set.insert(term);
    TypeNode tn = term.getType();
    Node skolem = NodeManager::currentNM()->mkSkolem(
        "ACKSKOLEM$$",
        tn,
        "is a variable created by the ackermannization "
        "preprocessing pass, for " + term.toString());
    fun_to_skolem.addSubstitution(term, skolem);
  }
}

void collectFunctionSymbols(
    TNode term,
    FunctionToArgsMap& fun_to_args,
    SubstitutionMap& fun_to_skolem,
    std::unordered_set<TNode, TNodeHashFunction>& seen)
{
  if (seen.find(term) != seen.end()) return;
  if (term.getKind() == kind::APPLY_UF)
  {
    storeFunction(term.getOperator(), term, fun_to_args, fun_to_skolem);
  }
  for (const TNode& n : term)
  {
    collectFunctionSymbols(n, fun_to_args, fun_to_skolem, seen);
  }
  seen.insert(term);
}

}  // namespace

/* -------------------------------------------------------------------------- */

Ackermann::Ackermann(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "ackermann"),
      d_funcToSkolem(preprocContext->getUserContext())
{
}

PreprocessingPassResult Ackermann::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  AlwaysAssert(!options::incrementalSolving());

  std::unordered_set<TNode, TNodeHashFunction> seen;

  for (const Node& a : assertionsToPreprocess->ref())
  {
    collectFunctionSymbols(a, d_funcToArgs, d_funcToSkolem, seen);
  }

  NodeManager* nm = NodeManager::currentNM();
  for (const auto& p : d_funcToArgs)
  {
    TNode func = p.first;
    const NodeSet& args = p.second;
    NodeSet::const_iterator it1 = args.begin();
    for (; it1 != args.end(); ++it1)
    {
      for (NodeSet::const_iterator it2 = it1; it2 != args.end(); ++it2)
      {
        TNode args1 = *it1;
        TNode args2 = *it2;
        Node args_eq;

        if (args1.getKind() == kind::APPLY_UF)
        {
          AlwaysAssert(args1.getKind() == kind::APPLY_UF
                       && args1.getOperator() == func);
          AlwaysAssert(args2.getKind() == kind::APPLY_UF
                       && args2.getOperator() == func);
          AlwaysAssert(args1.getNumChildren() == args2.getNumChildren());

          std::vector<Node> eqs(args1.getNumChildren());

          for (unsigned i = 0, n = args1.getNumChildren(); i < n; ++i)
          {
            eqs[i] = nm->mkNode(kind::EQUAL, args1[i], args2[i]);
          }
          args_eq = util::NaryBuilder::mkAssoc(kind::AND, eqs);
        }
        Node func_eq = nm->mkNode(kind::EQUAL, args1, args2);
        Node lemma = nm->mkNode(kind::IMPLIES, args_eq, func_eq);
        assertionsToPreprocess->push_back(lemma);
      }
    }
  }

  /* replace applications of UF by skolems */
  // FIXME for model building, github issue #1901
  for (unsigned i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    assertionsToPreprocess->replace(
        i, d_funcToSkolem.apply((*assertionsToPreprocess)[i]));
  }

  return PreprocessingPassResult::NO_CONFLICT;
}

/* -------------------------------------------------------------------------- */

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
