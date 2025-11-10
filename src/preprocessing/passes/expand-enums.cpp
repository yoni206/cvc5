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

#include "preprocessing/passes/expand-enums.h"

#include <cmath>

#include "base/check.h"
#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "smt/logic_exception.h"
#include "options/base_options.h"
#include "options/options.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"

using namespace cvc5::internal;
using namespace cvc5::internal::theory;

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

/* -------------------------------------------------------------------------- */



ExpandEnums::ExpandEnums(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "expand-enums")
{
}

PreprocessingPassResult ExpandEnums::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  for (unsigned i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
  }

  return PreprocessingPassResult::NO_CONFLICT;
}

/* -------------------------------------------------------------------------- */

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
