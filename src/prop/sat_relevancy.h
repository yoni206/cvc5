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
#include "context/cdo.h"
#include "context/cdqueue.h"
#include "expr/node.h"
#include "prop/sat_solver.h"
#include "theory/theory.h"
#include "util/statistics_registry.h"

namespace CVC4 {

class DecisionEngine;
class TheoryEngine;

namespace prop {

class CnfStream;
class CDCLTSatSolverInterface;

/** Properties of lemmas */
enum class RlvProperty : uint32_t
{
  NONE = 0,
  RLV_POS = 1,
  RLV_NEG = 2,
  ENQUEUED = 4,
  JUSTIFIED = 8,
  INPUT = 16
};
bool isRlvPropertyRlvPos(RlvProperty p);
bool isRlvPropertyRlvNeg(RlvProperty p);
bool isRlvPropertyEnqueued(RlvProperty p);
bool isRlvPropertyJustified(RlvProperty p);
bool isRlvPropertyInput(RlvProperty p);
/** Define operator lhs | rhs */
RlvProperty operator|(RlvProperty lhs, RlvProperty rhs);
/** Define operator lhs |= rhs */
RlvProperty& operator|=(RlvProperty& lhs, RlvProperty rhs);
/** Define operator lhs & rhs */
RlvProperty operator&(RlvProperty lhs, RlvProperty rhs);
/** Define operator lhs &= rhs */
RlvProperty& operator&=(RlvProperty& lhs, RlvProperty rhs);

class RlvInfo
{
 public:
  RlvInfo(context::Context* context)
      : d_parents(context),
        d_parentPol(context),
        d_childPol(context),
        d_rlvp(context, RlvProperty::NONE)
  {
  }
  ~RlvInfo() {}
  /** The parents that we impact */
  context::CDList<TNode> d_parents;
  /** The polarity of the parent */
  context::CDList<bool> d_parentPol;
  /** The child polarity in the parent */
  context::CDList<bool> d_childPol;
  /** The properties */
  context::CDO<RlvProperty> d_rlvp;
};

/**
 * SAT relevancy management
 */
class SatRelevancy
{
  typedef context::CDHashMap<TNode, std::shared_ptr<RlvInfo>, TNodeHashFunction>
      RlvMap;

 public:
  SatRelevancy(CDCLTSatSolverInterface* satSolver,
               context::Context* context,
               context::UserContext* userContext,
               CnfStream* cnfStream);

  ~SatRelevancy();
  /**
   * Notify preprocessed assertions, should be called before any calls to
   * notifyAsserted are made in the current SAT context.
   */
  void notifyAssertion(TNode assertion);
  /**
   * Notify that lem is a new lemma. This adds new literals that should be
   * asserted at this time to theory engine.
   *
   * The notification of lemmas is user-context dependent.
   */
  void notifyLemma(TNode lem, context::CDQueue<TNode>& queue);
  /**
   * Notify that lem is an activated skolem definition.
   *
   * The notification of lemmas is SAT-context dependent.
   */
  void notifyActivatedSkolemDef(TNode lem, context::CDQueue<TNode>& queue);
  /**
   * Notify that the SAT solver has asserted literal l, which may be a theory
   * atom or a formula. Adds the literals that should be asserted to the theory
   * engine at this time to queue.
   *
   * For example, if l is not relevant, this may add nothing to queue. If l is
   * a formula whose children are atoms and have already been asserted, this
   * may trigger multiple literals to be added to queue.
   */
  void notifyAsserted(const SatLiteral& l, context::CDQueue<TNode>& queue);
  /** check */
  void check(theory::Theory::Effort effort, context::CDQueue<TNode>& queue);
  /** notify decision request */
  void notifyDecisionRequest(TNode n, context::CDQueue<TNode>& queue);

 private:
  /** Get or mk rlv info */
  RlvInfo* getOrMkRlvInfo(TNode n);
  /**
   * Set that n is relevant, add new theory literals to assert to TheoryEngine
   * in queue.
   */
  void setRelevant(TNode n, bool pol, context::CDQueue<TNode>* queue);
  void setRelevantInternal(TNode n, bool pol, context::CDQueue<TNode>* queue);
  /**
   * Set that atom has been assigned a value that makes a child of parent equal
   * to "pol", where parent is a term that was waiting for the value of atom.
   *
   * Adds relevant literals to be asserted to queue.
   *
   * Return true if the assignment to atom that led to this method being
   * called is relevant.
   */
  bool setAssertedChild(TNode atom,
                        bool pol,
                        TNode parent,
                        bool ppol,
                        context::CDQueue<TNode>& queue);
  /** has SAT value, if node has a value, return true and set value */
  bool hasSatValue(TNode node, bool& value) const;
  /**
   * Add parent to the relevant waiting parents of n.
   */
  void addParentRlvWait(TNode n, bool pol, TNode parentAtom, bool ppol);
  /** Ensure lemmas relevant */
  void ensureLemmasRelevant(context::CDQueue<TNode>* queue);
  /** Pointer to the SAT solver */
  CDCLTSatSolverInterface* d_satSolver;
  /** Pointer to the SAT context */
  context::Context* d_context;
  /** pointer to the CNF stream */
  CnfStream* d_cnfStream;
  /**
   * The set of formulas that are asserted (user-context dependent).
   */
  context::CDList<TNode> d_asserted;
  /**
   * The set of asserted formulas that have been marked relevant (SAT-context
   * dependent).
   */
  context::CDHashSet<Node, NodeHashFunction> d_assertedRlv;
  /**
   * The set of formulas that are relevant. Polarity matters, no double
   * negations.
   */
  context::CDHashSet<Node, NodeHashFunction> d_rlvPos;
  context::CDHashSet<Node, NodeHashFunction> d_rlvNeg;
  /**
   * The set of formulas that have been justified that are in the range of
   * d_rlvWaitMap.
   *
   * Polarity matters, no double negations.
   */
  context::CDHashSet<Node, NodeHashFunction> d_justify;
  /**
   * The relevancy waiting map, for each (non-negated) formula.
   */
  RlvMap d_rlvMap;
  // debugging
  bool d_isActiveTmp;
  context::CDO<uint64_t> d_numAsserts;
  context::CDO<uint64_t> d_numAssertsRlv;
  /**
   */
  context::CDHashSet<Node, NodeHashFunction> d_enqueued;
};

}  // namespace prop
}  // namespace CVC4

#endif /* CVC4__PROP__SAT_RELEVANCY_H */
