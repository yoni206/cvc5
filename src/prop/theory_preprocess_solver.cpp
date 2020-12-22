/*********************                                                        */
/*! \file theory_preprocess_solver.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Theory preprocess solver
 **/
#include "prop/theory_preprocess_solver.h"

namespace CVC4 {
namespace prop {

TheoryPreprocessSolver::TheoryPreprocessSolver(
    PropEngine& propEngine,
    TheoryEngine& theoryEngine,
    context::UserContext* userContext,
    ProofNodeManager* pnm)
    : d_propEngine(propEngine),
      d_tpp(theoryEngine, userContext, pnm),
      d_rtf(d_tpp.getRemoveTermFormulas())
{
}

TheoryPreprocessSolver::~TheoryPreprocessSolver() {}

void TheoryPreprocessSolver::notifyAssertFact(TNode assertion)
{
  // do nothing
}

theory::TrustNode TheoryPreprocessSolver::preprocessLemma(
    theory::TrustNode trn,
    std::vector<theory::TrustNode>& ppLemmas,
    std::vector<Node>& ppSkolems)
{
  // use version with lemmas, use fixed point true
  return d_tpp.preprocessLemma(trn, ppLemmas, ppSkolems, true, true);
}

theory::TrustNode TheoryPreprocessSolver::preprocess(
    TNode node,
    std::vector<theory::TrustNode>& ppLemmas,
    std::vector<Node>& ppSkolems)
{
  // use version with lemmas, use fixed point true
  return d_tpp.preprocess(node, ppLemmas, ppSkolems, true, true);
}

theory::TrustNode TheoryPreprocessSolver::removeItes(
    TNode node,
    std::vector<theory::TrustNode>& ppLemmas,
    std::vector<Node>& ppSkolems)
{
  // run using the remove term formula utility directly, use fixed point true
  return d_rtf.run(node, ppLemmas, ppSkolems, true);
}

void TheoryPreprocessSolver::check(theory::Theory::Effort effort)
{
  // do nothing
}

}  // namespace prop
}  // namespace CVC4
