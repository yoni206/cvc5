/*********************                                                        */
/*! \file iand_solver.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Solver for integer and (IAND) constraints
 **/

#ifndef CVC4__THEORY__ARITH__IAND_SOLVER_H
#define CVC4__THEORY__ARITH__IAND_SOLVER_H

#include <map>
#include <unordered_map>
#include <utility>
#include <vector>

#include "context/cdhashset.h"
#include "context/cdinsert_hashmap.h"
#include "context/cdlist.h"
#include "context/cdqueue.h"
#include "context/context.h"
#include "expr/kind.h"
#include "expr/node.h"
#include "theory/arith/theory_arith.h"
#include "theory/arith/nl_model.h"

namespace CVC4 {
namespace theory {
namespace arith {

/** Integer and solver class
 *
 */
class IAndSolver
{
 public:
  IAndSolver(TheoryArith& containing, NlModel& model);
  ~IAndSolver();

  /** init last call
   *
   * This is called at the beginning of last call effort check, where
   * assertions are the set of assertions belonging to arithmetic,
   * false_asserts is the subset of assertions that are false in the current
   * model, and xts is the set of extended function terms that are active in
   * the current context.
   */
  void initLastCall(const std::vector<Node>& assertions,
                    const std::vector<Node>& false_asserts,
                    const std::vector<Node>& xts);
  //-------------------------------------------- lemma schemas

  //-------------------------------------------- end lemma schemas
 private:
  // The theory of arithmetic containing this extension.
  TheoryArith& d_containing;
  /** Reference to the non-linear model object */
  NlModel& d_model;
  /** commonly used terms */
  Node d_zero;
  Node d_one;
  Node d_neg_one;
  Node d_two;
  Node d_true;
  Node d_false;
  /** all IAND terms */
  std::map< unsigned, std::vector< Node > > d_iands;
}; /* class IAndSolver */

}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__ARITH__IAND_SOLVER_H */
