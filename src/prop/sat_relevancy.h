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
#include "context/cdlist.h"
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

class RlvWaitInfo
{
 public:
  RlvWaitInfo(context::Context* context) : d_parents(context) {}
  ~RlvWaitInfo() {}
  /** The parents that we impact */
  context::CDList<Node> d_parents;
};

/**
 * SAT relevancy management
 */
class SatRelevancy
{
  typedef context::
      CDHashMap<Node, std::shared_ptr<RlvWaitInfo>, NodeHashFunction>
          RlvWaitMap;

 public:
  SatRelevancy(DPLLSatSolverInterface* satSolver,
               context::Context* context,
               CnfStream* cnfStream);

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
  void setRelevant(TNode n, bool pol, context::CDQueue<TNode>* queue);
  /**
   * Set that atom has been assigned pol, where parent is a term that was
   * waiting for the value of atom.
   *
   * Adds relevant literals to be asserted to queue.
   */
  void setAssertedChild(TNode atom,
                        bool pol,
                        Node parent,
                        context::CDQueue<TNode>& queue);
  /** has SAT value, if node has a value, return true and set value */
  bool hasSatValue(TNode node, bool& value) const;
  /** Get or make relevancy wait info */
  RlvWaitInfo* getOrMkRlvWaitInfo(TNode n);
  /** Pointer to the SAT solver */
  DPLLSatSolverInterface* d_satSolver;
  /** Pointer to the SAT context */
  context::Context* d_context;
  /** pointer to the CNF stream */
  CnfStream* d_cnfStream;
  /**
   * The set of formulas that are relevant. Polarity matters, no double
   * negations.
   */
  context::CDHashSet<Node, NodeHashFunction> d_rlv;
  /**
   * The relevancy waiting map, for each (non-negated) formula.
   */
  RlvWaitMap d_rlvWaitMap;
};

}  // namespace prop
}  // namespace CVC4

#endif /* CVC4__PROP__SAT_RELEVANCY_H */
