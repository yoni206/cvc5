/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of bit-vector conversions solver.
 */

#include "theory/uf/conversions_solver.h"

#include "options/uf_options.h"
#include "theory/arith/arith_utilities.h"
#include "theory/theory_inference_manager.h"
#include "theory/theory_model.h"
#include "theory/theory_state.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace uf {

ConversionsSolver::ConversionsSolver(Env& env,
                                     TheoryState& state,
                                     TheoryInferenceManager& im)
    : EnvObj(env),
      d_state(state),
      d_im(im),
      d_preRegistered(userContext()),
      d_reduced(userContext())
{
}

ConversionsSolver::~ConversionsSolver() {}

void ConversionsSolver::preRegisterTerm(TNode term)
{
  d_preRegistered.push_back(term);
}

void ConversionsSolver::check()
{
  Trace("bv-convs") << "Bitvector conversion terms : " << std::endl;
  Trace("bv-convs") << "ConversionsSolver: Check reductions for "
                    << d_preRegistered.size() << " terms" << std::endl;
  // check reductions for all bv conversion terms
  for (const Node& a : d_preRegistered)
  {
    checkReduction(a);
  }
}

void ConversionsSolver::checkReduction(Node n)
{
  Trace("bv-convs") << "Check reduction " << n << std::endl;
  if (d_reduced.find(n) != d_reduced.end())
  {
    Trace("bv-convs") << "...already reduced" << std::endl;
    return;
  }
  // check whether it already has the correct value in the model?
  Node val = d_state.getModel()->getValue(n);
  Node uval = d_state.getRepresentative(n);
  Trace("bv-convs-debug") << "  model value = " << val << std::endl;
  Trace("bv-convs-debug") << "          rep = " << uval << std::endl;
  if (val == uval)
  {
    // "model-based reduction" strategy, do not reduce things that already have
    // correct model values
    Trace("bv-convs") << "...already correct in model" << std::endl;
    return;
  }
  NodeManager* nm = NodeManager::currentNM();
  if (options().uf.arithBvConvMode == options::ArithBVConvMode::VALUES)
  {
    Node argval = d_state.getModel()->getValue(n[0]);
    Trace("bv-convs-debug") << "  arg value = " << argval << std::endl;
    Node eval = rewrite(nm->mkNode(n.getOperator(), argval));
    Trace("bv-convs-debug") << "  evaluated = " << eval << std::endl;
    Node lem = nm->mkNode(Kind::IMPLIES, n[0].eqNode(argval), n.eqNode(eval));
    d_im.lemma(lem, InferenceId::UF_ARITH_BV_CONV_VALUE_REFINE);


    return;
  }


  if ((options().uf.arithBvConvMode == options::ArithBVConvMode::LEMMAS) && n.getKind() == Kind::BITVECTOR_TO_NAT) {
    Node zero = nm->mkConstInt(Rational(0));
    uint32_t k = n[0].getType().getBitVectorSize();
    Node max_val = nm->mkConstInt(Rational(Integer(2).pow(k)));

    Node lower_bound = nm->mkNode(Kind::LEQ, zero, n);
    Node upper_bound = nm->mkNode(Kind::LEQ, n, max_val);
    Node range_lemma = nm->mkNode(Kind::AND, lower_bound, upper_bound);
    std::cout << "panda " << d_state.getModel()->getValue(range_lemma)  << std::endl;
    //if (d_state.getModel()->getValue(range_lemma) == nm->mkConst(false)) 
    {
      d_im.lemma(range_lemma, InferenceId::UF_ARITH_BV_CONV_RANGE);
      return;
    }
  }

  Node lem;
  Kind k = n.getKind();
  if (k == Kind::BITVECTOR_TO_NAT)
  {
    lem = arith::eliminateBv2Nat(n);
  }
  else if (k == Kind::INT_TO_BITVECTOR)
  {
    lem = arith::eliminateInt2Bv(n);
  }
  lem = n.eqNode(lem);
  d_im.lemma(lem, InferenceId::UF_ARITH_BV_CONV_REDUCTION);
  d_reduced.insert(n);
  Trace("bv-convs") << "...do reduction" << std::endl;
}

}  // namespace uf
}  // namespace theory
}  // namespace cvc5::internal
