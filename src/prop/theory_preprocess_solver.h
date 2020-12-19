/*********************                                                        */
/*! \file theory_preprocess_solver.h
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

#include "cvc4_private.h"

#ifndef CVC4__PROP__THEORY_PREPROCESS_SOLVER_H
#define CVC4__PROP__THEORY_PREPROCESS_SOLVER_H

#include <vector>

#include "context/cdhashmap.h"
#include "expr/node.h"
#include "theory/theory_preprocessor.h"
#include "theory/trust_node.h"

namespace CVC4 {

class TheoryEngine;

namespace prop {

/**
 * The class that manages theory preprocessing and how it relates to lemma
 * generation.
 */
class TheoryPreprocessSolver
{
  using NodeNodeMap = context::CDHashMap<Node, Node, NodeHashFunction>;

 public:
  TheoryPreprocessSolver(TheoryEngine* theoryEngine,
                         context::UserContext* userContext,
                         ProofNodeManager* pnm = nullptr);

  ~TheoryPreprocessSolver();

  /**
   * Assert fact
   */
  Node assertFact(TNode assertion,
                  std::vector<theory::TrustNode>& newLemmas,
                  std::vector<Node>& newSkolems);

  /**
   * Call the preprocessor on node, return trust node corresponding to the
   * rewrite.
   */
  theory::TrustNode preprocessLemma(theory::TrustNode trn,
                                    std::vector<theory::TrustNode>& newLemmas,
                                    std::vector<Node>& newSkolems,
                                    bool doTheoryPreprocess);
  /**
   * Call the preprocessor on node, return trust node corresponding to the
   * rewrite.
   */
  theory::TrustNode preprocess(TNode node,
                               std::vector<theory::TrustNode>& newLemmas,
                               std::vector<Node>& newSkolems,
                               bool doTheoryPreprocess);

 private:
  /**
   * Convert lemma to the form to send to the CNF stream. This means mapping
   * back to unpreprocessed form.
   *
   * It should be the case that convertLemmaToProp(preprocess(n)) = n.
   */
  theory::TrustNode convertLemmaToProp(theory::TrustNode lem);
  /**
   * Convert lemma to the form to send to the CNF stream.
   */
  Node convertLemmaToPropInternal(Node lem) const;
  /** The theory preprocessor */
  theory::TheoryPreprocessor d_tpp;
  /** Map from preprocessed atoms to their unpreprocessed form */
  NodeNodeMap d_ppLitMap;
}; /* class TheoryPreprocessSolver */

}  // namespace prop
}  // namespace CVC4

#endif /* CVC4__PROP__THEORY_PREPROCESS_SOLVER_H */
