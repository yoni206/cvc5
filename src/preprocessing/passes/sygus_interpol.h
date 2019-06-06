/*********************                                                        */
/*! \file sygus_interpol.h
 ** \verbatim
 ** Top contributors (to current version):
 ** Andrew Reynolds, Yoni Zohar
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Sygus interpolation preprocessing pass, which transforms an arbitrary
 ** input into an interpolation problem. Heavily based on sygus_abduct.h
 **
 **/

#ifndef CVC4__PREPROCESSING__PASSES__SYGUS_INTERPOL_H
#define CVC4__PREPROCESSING__PASSES__SYGUS_INTERPOL_H

#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

/** SygusInterpol
 *
 * A preprocessing utility that turns a set of quantifier-free assertions into
 * a sygus conjecture that encodes an interpolation problem. In detail, 
 * assume our input formula is F( x ) for free symbols x, and is
 * partitioned into axioms Fa and negated conjecture Fc
 * then the sygus conjecture we construct is:
 
 * exists A. forall x. ( (Fa( x ) => A( x ))  ^ (A( x ) => Fc( x )) )
 *
 * where A( x ) is a predicate over the free symbols of our input that are shared between
 * Fa and Fc.
 * In other words, A( x ) must be implied by our axioms Fa and imply
 * Fc( x ). We encode this conjecture using SygusSideConditionAttribute.
 */
class SygusInterpol : public PreprocessingPass
{
 public:
  SygusInterpol(PreprocessingPassContext* preprocContext);

 protected:
  /**
   * Replaces the set of assertions by an interpolation sygus problem described
   * above.
   */
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4

#endif /* CVC4__PREPROCESSING__PASSES__SYGUS_INTERPOL_H_ */
