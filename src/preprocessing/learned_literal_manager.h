/*********************                                                        */
/*! \file learned_literal_manager.h
 ** \verbatim
 ** Top contributors (to current version):
 **   AAndrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The learned literal manager
 **/

#include "cvc4_private.h"

#ifndef CVC4__PREPROCESSING__LEARNED_LITERAL_MANAGER_H
#define CVC4__PREPROCESSING__LEARNED_LITERAL_MANAGER_H

#include "context/cdhashmap.h"
#include "smt/smt_engine.h"
#include "expr/node.h"

namespace CVC4 {
namespace preprocessing {

class LearnedLiteralManager
{
 public:
  LearnedLiteralManager(
      SmtEngine* smt, context::UserContext * u);

  SmtEngine* getSmt() { return d_smt; }
  /** 
   * Process learned literal. This method is called when a literal is
   * entailed by the current set of assertions.
   * 
   * It should be rewritten, and such that top level substitutions have
   * been applied to it.
   */
  void notifyLearnedLiteral(Node lit);
  /** Get learned literals */
  std::vector<Node>& getLearnedLiterals();
 private:
  /** Pointer to the SmtEngine that this context was created in. */
  SmtEngine* d_smt;
  /** Learned literals */
  context::CDHashMap<Node, bool, NodeHashFunction> d_learnedLits;
  /** Current */
  std::vector<Node> d_currLearnedLits;
}; 

}  // namespace preprocessing
}  // namespace CVC4

#endif /* CVC4__PREPROCESSING__LEARNED_LITERAL_MANAGER_H */
