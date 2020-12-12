/*********************                                                        */
/*! \file theory_preprocess_manager.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Theory preprocess manager
 **/

#include "cvc4_private.h"

#ifndef CVC4__PROP__THEORY_PREPROCESS_MANAGER_H
#define CVC4__PROP__THEORY_PREPROCESS_MANAGER_H

#include "theory/theory_preprocessor.h"
#include "expr/node.h"
#include "util/statistics_registry.h"
#include "theory/trust_node.h"

namespace CVC4 {
namespace prop {

/**
 * Manages theory preprocessing between TheoryEngine and PropEngine.
 */
class TheoryPreprocessManager
{
 public:
  TheoryPreprocessManager(TheoryEngine& engine,
                     RemoveTermFormulas& tfr,
                     context::UserContext* userContext,
                     ProofNodeManager* pnm = nullptr);
  ~TheoryPreprocessManager();
  
  /** 
   * Call the preprocessor on node, return trust node corresponding to the
   * rewrite.
   */
  TrustNode preprocess(TNode node,
                       std::vector<TrustNode>& newLemmas,
                       std::vector<Node>& newSkolems,
                       bool doTheoryPreprocess);
  
  /** 
   * Convert lemma to the form to send to the CNF stream. This means mapping
   * back to unpreprocessed form.
   * 
   * It should be the case that convertLemmaToProp(preprocess(n)) = n.
   */
  TrustNode convertLemmaToProp(TrustNode lem);
private:
  /** 
   * Convert lemma to the form to send to the CNF stream.
   */
  Node convertLemmaToPropInternal(Node lem) const;
  /** The theory preprocessor */
  theory::TheoryPreprocessor d_tpp;
  /** Map from preprocessed atoms to their unpreprocessed form */
  NodeNodeMap d_ppLitMap;
};

}  // namespace prop
}  // namespace CVC4

#endif /* CVC4__PROP__SAT_RELEVANCY_H */
