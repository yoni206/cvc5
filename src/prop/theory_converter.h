/*********************                                                        */
/*! \file theory_converter.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Theory converter
 **/

#include "cvc4_private.h"

#ifndef CVC4__PROP__THEORY_CONVERTER_H
#define CVC4__PROP__THEORY_CONVERTER_H

#include "context/cdhashmap.h"
#include "theory/theory_preprocessor.h"
#include "expr/node.h"
#include "util/statistics_registry.h"
#include "theory/trust_node.h"

namespace CVC4 {
namespace prop {

/**
 * Manages theory preprocessing conversions between TheoryEngine and PropEngine.
 */
class TheoryConverter
{
  using NodeNodeMap = context::CDHashMap<Node, Node, NodeHashFunction>;
 public:
  TheoryConverter(TheoryEngine& engine,
                     context::UserContext* userContext,
                     ProofNodeManager* pnm = nullptr);
  ~TheoryConverter();
  
  /** 
   * Call the preprocessor on node, return trust node corresponding to the
   * rewrite.
   */
  theory::TrustNode preprocess(TNode node,
                       std::vector<theory::TrustNode>& newLemmas,
                       std::vector<Node>& newSkolems,
                       bool doTheoryPreprocess);
  
  /** 
   * Convert lemma to the form to send to the CNF stream. This means mapping
   * back to unpreprocessed form.
   * 
   * It should be the case that convertLemmaToProp(preprocess(n)) = n.
   */
  theory::TrustNode convertLemmaToProp(theory::TrustNode lem);
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
