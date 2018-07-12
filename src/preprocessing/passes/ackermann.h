/*********************                                                        */
/*! \file ackermann.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz
 **   Yoni Zohar
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Ackermannization preprocessing pass.
 **
 **/

#include "cvc4_private.h"

#ifndef __CVC4__PREPROCESSING__PASSES__ACKERMANN_H
#define __CVC4__PREPROCESSING__PASSES__ACKERMANN_H

#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"

#include <unordered_map>

namespace CVC4 {
namespace preprocessing {
namespace passes {

typedef std::unordered_map<Node, NodeSet, NodeHashFunction> FunctionToArgsMap;

class Ackermann : public PreprocessingPass
{
 public:
   Ackermann(PreprocessingPassContext* preprocContext);

 protected:
  /**
   * Apply Ackermannization as follows:
   *
   * - For each application f(X) where X = (x1, . . . , xn), introduce a fresh
   *   variable f_X and use it to replace all occurrences of f(X).
   *
   * - For each f(X) and f(Y) with X = (x1, . . . , xn) and Y = (y1, . . . , yn)
   *   occurring in the input formula, add the following lemma:
   *     (x_1 = y_1 /\ ... /\ x_n = y_n) => f_X = f_Y
   */
   PreprocessingPassResult applyInternal(
       AssertionPipeline* assertionsToPreprocess) override;

 private:
  FunctionToArgsMap d_funcToArgs;
  theory::SubstitutionMap d_funcToSkolem;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4

#endif
