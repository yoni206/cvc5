/*********************                                                        */
/*! \file lazy_tpp_solver.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The lazy theory preprocess solver
 **/
#include "prop/lazy_tpp_solver.h"

#include "prop/prop_engine.h"

namespace CVC4 {
namespace prop {

LazyTppSolver::LazyTppSolver(PropEngine& propEngine,
                             TheoryEngine& theoryEngine,
                             context::UserContext* userContext,
                             ProofNodeManager* pnm)
    : TheoryPreprocessSolver(propEngine, theoryEngine, userContext, pnm),
      d_processedSkolems(userContext)
{
}

LazyTppSolver::~LazyTppSolver() {}

void LazyTppSolver::notifyAssertFact(TNode assertion)
{
  // determine which skolems become activated, these will be processed
  // immediately after this call in check(...).
  d_rtf.getSkolems(assertion, d_activeSkolems);
}

theory::TrustNode LazyTppSolver::preprocessLemma(
    theory::TrustNode trn,
    std::vector<theory::TrustNode>& newLemmas,
    std::vector<Node>& newSkolems,
    bool doTheoryPreprocess)
{
  // version without fixed point or lemmas
  return d_tpp.preprocessLemma(trn, doTheoryPreprocess);
}

theory::TrustNode LazyTppSolver::preprocess(
    TNode node,
    std::vector<theory::TrustNode>& newLemmas,
    std::vector<Node>& newSkolems,
    bool doTheoryPreprocess)
{
  // version without fixed point or lemmas
  return d_tpp.preprocess(node, doTheoryPreprocess);
}

void LazyTppSolver::check(theory::Theory::Effort effort)
{
  // add lemmas for each skolem
  for (const Node& k : d_activeSkolems)
  {
    if (d_processedSkolems.find(k) != d_processedSkolems.end())
    {
      continue;
    }
    theory::TrustNode lem = d_rtf.getLemmaForSkolem(k);

    // TODO: add lemma to prop engine

    // newSkolems.push_back(k);
    d_processedSkolems.insert(k);
  }
  d_activeSkolems.clear();
}

}  // namespace prop
}  // namespace CVC4
