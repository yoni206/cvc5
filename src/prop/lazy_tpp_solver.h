/*********************                                                        */
/*! \file lazy_tpp_solver.h
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

#include "cvc4_private.h"

#ifndef CVC4__PROP__LAZY_TPP_SOLVER_H
#define CVC4__PROP__LAZY_TPP_SOLVER_H

#include <vector>

#include "context/cdhashmap.h"
#include "expr/node.h"
#include "prop/theory_preprocess_solver.h"
#include "theory/trust_node.h"

namespace CVC4 {
namespace prop {

/**
 */
class LazyTppSolver : public TheoryPreprocessSolver
{
  using NodeNodeMap = context::CDHashMap<Node, Node, NodeHashFunction>;

 public:
  LazyTppSolver(TheoryEngine& theoryEngine,
                context::UserContext* userContext,
                ProofNodeManager* pnm = nullptr);

  ~LazyTppSolver();

  /**
   * Assert fact, returns the (possibly preprocessed) version of the assertion,
   * as well as indicating any new lemmas that should be asserted.
   */
  Node assertFact(TNode assertion,
                  std::vector<theory::TrustNode>& newLemmas,
                  std::vector<Node>& newSkolems) override;

  /**
   * Call the preprocessor on node, return trust node corresponding to the
   * rewrite.
   */
  theory::TrustNode preprocessLemma(theory::TrustNode trn,
                                    std::vector<theory::TrustNode>& newLemmas,
                                    std::vector<Node>& newSkolems,
                                    bool doTheoryPreprocess) override;
  /**
   * Call the preprocessor on node, return REWRITE trust node corresponding to
   * the rewrite.
   */
  theory::TrustNode preprocess(TNode node,
                               std::vector<theory::TrustNode>& newLemmas,
                               std::vector<Node>& newSkolems,
                               bool doTheoryPreprocess) override;

  /**
   * Convert lemma to the form to send to the CNF stream. This means mapping
   * back to unpreprocessed form.
   *
   * It should be the case that convertLemmaToProp(preprocess(n)) = n.
   */
  theory::TrustNode convertToPropLemma(theory::TrustNode lem) override;
  /**
   * Convert to prop
   */
  theory::TrustNode convertToProp(TNode n) override;

 private:
  /** convert literal to theory internal */
  Node convertToTheoryInternal(TNode assertion);
  /** convert literal to prop internal */
  Node convertToPropInternal(TNode assertion);
  /**
   * Convert lemma to the form to send to the CNF stream.
   */
  Node convertFormulaToPropInternal(TNode lem) const;
  /** Map from preprocessed atoms to their unpreprocessed form */
  NodeNodeMap d_ppLitMap;
};

}  // namespace prop
}  // namespace CVC4

#endif /* CVC4__PROP__LAZY_TPP_SOLVER_H */
