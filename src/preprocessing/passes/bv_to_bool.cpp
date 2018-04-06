/*********************                                                        */
/*! \file bv_to_bool.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Yoni Zohar
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The bvToBool preprocessing pass
 **
 ** Lifts unary bitvectors to booleans.
 **/

#include "preprocessing/passes/bv_to_bool.h"

#include <string>
#include <unordered_map>
#include <vector>

#include "expr/node.h"
#include "theory/rewriter.h"
#include "theory/theory.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

using namespace CVC4::theory;

using NodeMap = std::unordered_map<Node, Node, NodeHashFunction>;


Node BVToBool::bvToBool(TNode node) {
  Trace("bv-to-bool") << "bvToBool" << endl;
  //TODO need to expose ResourceManager from SmtEngine in order to make the next line possible.
  //  d_preprocContext->getSmt()->getResourceManager()->spendResource(options::preprocessStep());
  Assert(false);
  return Rewriter::rewrite(d_preprocContext->getTheoryEngine()->ppBvToBool(node));
}


BVToBool::BVToBool(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "bv-to-bool"){};

PreprocessingPassResult BVToBool::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{  
 for (unsigned i = 0; i < assertionsToPreprocess->size(); ++i)
  {
    assertionsToPreprocess->replace(
        i, bvToBool((*assertionsToPreprocess)[i]));
  }
  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
