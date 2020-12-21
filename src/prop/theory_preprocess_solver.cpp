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
    TheoryEngine& theoryEngine,
    context::UserContext* userContext,
    ProofNodeManager* pnm)
    : d_tpp(theoryEngine, userContext, pnm),
      d_rtf(d_tpp.getRemoveTermFormulas())
{
}

TheoryPreprocessSolver::~TheoryPreprocessSolver() {}

Node TheoryPreprocessSolver::assertFact(
    TNode assertion,
    std::vector<theory::TrustNode>& newLemmas,
    std::vector<Node>& newSkolems)
{
  // we do not change the assertion.
  return assertion;
}

theory::TrustNode TheoryPreprocessSolver::preprocessLemma(
    theory::TrustNode trn,
    std::vector<theory::TrustNode>& newLemmas,
    std::vector<Node>& newSkolems,
    bool doTheoryPreprocess)
{
  // use fixed point
  return d_tpp.preprocessLemma(
      trn, newLemmas, newSkolems, doTheoryPreprocess, true);
}

theory::TrustNode TheoryPreprocessSolver::preprocess(
    TNode node,
    std::vector<theory::TrustNode>& newLemmas,
    std::vector<Node>& newSkolems,
    bool doTheoryPreprocess)
{
  // use fixed point
  return d_tpp.preprocess(
      node, newLemmas, newSkolems, doTheoryPreprocess, true);
}

theory::TrustNode TheoryPreprocessSolver::convertToPropLemma(
    theory::TrustNode lem)
{
  // no change, since the PropEngine's literals are theory preprocessed.
  return lem;
}

theory::TrustNode TheoryPreprocessSolver::convertToProp(TNode n)
{
  // no change, since the PropEngine's literals are theory preprocessed.
  return theory::TrustNode::null();
}

}  // namespace prop
}  // namespace CVC4
