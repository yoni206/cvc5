/*********************                                                        */
/*! \file delay_expand_def.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Caleb Donovick
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Delayed expand definitions
 **/

#include "preprocessing/passes/delay_expand_def.h"

#include "expr/skolem_manager.h"
#include "theory/rewriter.h"

using namespace CVC4::theory;

namespace CVC4 {
namespace preprocessing {
namespace passes {

DelayExpandDefs::DelayExpandDefs(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "delay-expand-def"){};

PreprocessingPassResult DelayExpandDefs::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  size_t size = assertionsToPreprocess->size();
  for (size_t i = 0; i < size; ++i)
  {
    Node prev = (*assertionsToPreprocess)[i];
    TrustNode trn = expandDefinitions(prev);
    Node next = trn.isNull() ? prev : trn.getNode();
    Trace("delay-exp-def-assert") << "DelayExpandDefs: assert: " << next << std::endl;
    Node nextr = Rewriter::rewrite(next);
    if (prev!=nextr)
    {
      if (next!=nextr)
      {
        Trace("delay-exp-def-assert") << ".......................: " << nextr << std::endl;
      }
      assertionsToPreprocess->replace(i, nextr);
    }
  }
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  // We also must ensure that all purification UF are defined. This is
  // to ensure that all are replaced in e.g. terms in models.
  std::vector<Node> ufs = sm->getPurifyKindUfs();
  SmtEngine* smt = d_preprocContext->getSmt();
  for (const Node& uf : ufs)
  {
    Expr ufe = uf.toExpr();
    // define the function
    if (!smt->isDefinedFunction(ufe))
    {
      Node w = SkolemManager::getWitnessForm(uf);
      Assert(w.getKind() == kind::WITNESS);
      Node wr = Rewriter::rewrite(w);
      Assert(wr.getKind() == kind::LAMBDA);
      Trace("delay-exp-def-debug") << "Define " << uf << " based on " << w << " --> " << wr << std::endl;
      std::vector<Expr> args;
      for (const Node& wc : wr[0])
      {
        args.push_back(wc.toExpr());
      }
      smt->defineFunction(ufe, args, wr[1].toExpr(), true);
    }
  }

  return PreprocessingPassResult::NO_CONFLICT;
}

TrustNode DelayExpandDefs::expandDefinitions(Node n)
{
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  std::unordered_map<TNode, Node, TNodeHashFunction> visited;
  std::unordered_map<TNode, Node, TNodeHashFunction>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);

    if (it == visited.end())
    {
      visited[cur] = Node::null();
      visit.push_back(cur);
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
    else if (it->second.isNull())
    {
      Node ret = cur;
      bool needsRcons = false;
      std::vector<Node> children;
      if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        children.push_back(cur.getOperator());
      }
      for (const Node& cn : cur)
      {
        it = visited.find(cn);
        Assert(it != visited.end());
        Assert(!it->second.isNull());
        needsRcons = needsRcons || cn != it->second;
        children.push_back(it->second);
      }
      if (cur.getKind() == kind::APPLY_UF)
      {
        Node op = children[0];
        // maybe its a purification for kind?
        Kind pk = sm->getPurifyKindForUf(op);
        if (pk != kind::UNDEFINED_KIND)
        {
          Node pOp = sm->getPurifyKindOpForUf(op);
          if (pOp.isNull())
          {
            children.erase(children.begin(), children.begin() + 1);
          }
          else
          {
            children[0] = pOp;
          }
          ret = nm->mkNode(pk, children);
          needsRcons = false;
        }
      }
      if (needsRcons)
      {
        ret = nm->mkNode(cur.getKind(), children);
      }
      visited[cur] = ret;
    }
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());
  Assert(!visited.find(n)->second.isNull());
  return TrustNode::mkTrustRewrite(n, visited[n], nullptr);
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
