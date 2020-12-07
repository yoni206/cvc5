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
#include "expr/node.h"
#include "util/statistics_registry.h"
#include "context/cdqueue.h"
#include "prop/sat_solver.h"

namespace CVC4 {

class DecisionEngine;
class TheoryEngine;

namespace prop {

class CnfStream;

/**
 * The proxy class that allows the SatSolver to communicate with the theories
 */
class SatRelevancy
{
 public:
  SatRelevancy(context::Context* context,
              CnfStream* cnfStream);

  ~SatRelevancy();
  
  /**
   * Enqueue theory literals
   */
  void enqueueTheoryLiterals(const SatLiteral& l, context::CDQueue<TNode>& queue);
};

}/* CVC4::prop namespace */
}/* CVC4 namespace */

#endif /* CVC4__PROP__SAT_RELEVANCY_H */
