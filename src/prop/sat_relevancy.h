/*********************                                                        */
/*! \file sat_relevancy.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Sat relevancy module
 **/

#include "cvc4_private.h"

#ifndef CVC4__PROP__SAT_RELEVANCY_H
#define CVC4__PROP__SAT_RELEVANCY_H

#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "context/cdqueue.h"
#include "expr/node.h"
#include "prop/sat_solver.h"
#include "util/statistics_registry.h"

namespace CVC4 {

class DecisionEngine;
class TheoryEngine;

namespace prop {

class CnfStream;
class DPLLSatSolverInterface;

/**
 * SAT relevancy management
 */
class SatRelevancy
{
 public:
  SatRelevancy(DPLLSatSolverInterface* satSolver,
              context::Context* context, CnfStream* cnfStream);

  ~SatRelevancy();
  /**
   * Notify preprocessed assertions, should be called before any calls to
   * notifyAsserted are made in the current SAT context.
   */
  void notifyPreprocessedAssertions(const std::vector<Node>& assertions);
  /**
   * Notify that lem is a new lemma
   */
  void notifyNewLemma(TNode lem, context::CDQueue<TNode>& queue);
  /**
   * Enqueue theory literals
   */
  void notifyAsserted(const SatLiteral& l, context::CDQueue<TNode>& queue);

 private:
  /** 
   * Set that n is relevant, add new theory literals to assert to TheoryEngine
   * in queue.
   */
  void setRelevant(TNode n, context::CDQueue<TNode>* queue);
  /** has SAT value, if node has a value, return true and set value */
  bool hasValue(TNode node, bool& value) const;
  /** Reference to the parent prop engine */
  DPLLSatSolverInterface * d_propEngine;
  /** pointer to the CNF stream */
  CnfStream* d_cnfStream;
  /** A status for nodes */
  enum class RelevancyStatus : uint32_t
  {
    ASSERTED,
    RELEVANT,
    ASSERTED_AND_RELEVANT,
    NONE,
  };
  /** Mapping to the status */
  context::CDHashMap<Node, RelevancyStatus, NodeHashFunction> d_status;
  /** Mapping to the status */
  context::CDHashSet<Node, NodeHashFunction> d_rlv;
};

}  // namespace prop
}  // namespace CVC4

#endif /* CVC4__PROP__SAT_RELEVANCY_H */
