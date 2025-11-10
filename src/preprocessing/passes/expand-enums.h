/******************************************************************************
 * Top contributors (to current version):
 *   Yoni Zohar
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * expand-eums preprocessing pass.
 *
 * This implements eliminations of datatypes enums,
 * by instantiating the enum values.
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES_EXPAND_ENUMS_H
#define CVC5__PREPROCESSING__PASSES__EXPAND_ENUMS_H

#include <unordered_map>

#include "expr/node.h"
#include "preprocessing/preprocessing_pass.h"
#include "theory/logic_info.h"
#include "theory/substitutions.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

using TNodeSet = std::unordered_set<TNode>;

class ExpandEnums: public PreprocessingPass
{
 public:
  ExpandEnums(PreprocessingPassContext* preprocContext);

 protected:
  /**
   * Apply instantiations of enums
   */
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;

 private:

};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__PASSES__EXPAND_ENUMS_H */
