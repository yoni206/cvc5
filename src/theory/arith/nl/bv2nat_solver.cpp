/******************************************************************************
 * Top contributors (to current version):
 *   Yoni Zohar
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of a bv2nat solver.
 */

#include "theory/arith/nl/bv2nat_solver.h"

#include "options/arith_options.h"
#include "options/smt_options.h"
#include "preprocessing/passes/bv_to_int.h"
#include "theory/arith/arith_msum.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/inference_manager.h"
#include "theory/arith/nl/nl_model.h"
#include "theory/rewriter.h"
#include "util/bitvector.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {

BV2NatSolver::BV2NatSolver(Env& env,
                       InferenceManager& im,
                       NlModel& model)
    : EnvObj(env),
      d_im(im),
      d_model(model),
      d_initRefine(userContext())
{
  NodeManager* nm = nodeManager();
  d_false = nm->mkConst(false);
  d_true = nm->mkConst(true);
  d_zero = nm->mkConstInt(Rational(0));
  d_one = nm->mkConstInt(Rational(1));
  d_two = nm->mkConstInt(Rational(2));
}

BV2NatSolver::~BV2NatSolver() {}

void BV2NatSolver::initLastCall(const std::vector<Node>& assertions,
                              const std::vector<Node>& false_asserts,
                              const std::vector<Node>& xts)
{
  d_bv2nats.clear();

  Trace("bv2nat-mv") << "BV2NAT terms : " << std::endl;
  for (const Node& a : xts)
  {
    Kind ak = a.getKind();
    if (ak != Kind::BITVECTOR_TO_NAT)
    {
      // don't care about other terms
      continue;
    }
    size_t bsize = a[0].getType().getBitVectorSize();
    d_bv2nats[bsize].push_back(a);
    Trace("bv2nat-mv") << "- " << a << std::endl;
  }
}

void BV2NatSolver::checkInitialRefine()
{
  Trace("bv2nat-check") << "BV2NatSolver::checkInitialRefine" << std::endl;
  NodeManager* nm = nodeManager();
  for (const std::pair<const unsigned, std::vector<Node> >& is : d_bv2nats)
  {
    // the reference bitwidth
    unsigned k = is.first;
    for (const Node& i : is.second)
    {
      if (d_initRefine.find(i) != d_initRefine.end())
      {
        // already sent initial axioms for i in this user context
        continue;
      }
      d_initRefine.insert(i);
      Node op = i.getOperator();
      uint32_t bsize = i.getType().getBitvectorSize();
      Node twok = nm->mkConstInt(Rational(Integer(2).pow(bsize)));
      Node arg0Mod = nm->mkNode(Kind::INTS_MODULUS, i[0], twok);
      // initial refinement lemmas
      std::vector<Node> conj;
      // 0 <= bv2nat x < 2^k
      conj.push_back(nm->mkNode(Kind::LEQ, d_zero, i));
      conj.push_back(nm->mkNode(Kind::LT, i, rewrite(nm->mkNode(Kind::POW, d_two, nm->mkConstInt(Rational(k)));)));
      Node lem = conj.size() == 1 ? conj[0] : nm->mkNode(Kind::AND, conj);
      Trace("bv2nat-lemma") << "BV2NatSolver::Lemma: " << lem << " ; INIT_REFINE"
                          << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_BV2NAT_INIT_REFINE);
    }
  }
}

void BV2NatSolver::checkFullRefine()
{
  Trace("bv2nat-check") << "BV2NatSolver::checkFullRefine";
  Trace("bv2nat-check") << "BV2NAT terms: " << std::endl;
  for (const std::pair<const unsigned, std::vector<Node> >& is : d_bv2nats)
  {
    // the reference bitwidth
    unsigned k = is.first;
    for (const Node& i : is.second)
    {
      Node valBV2Natx = d_model.computeAbstractModelValue(i);
      Node valBV2NatxC = d_model.computeConcreteModelValue(i);
      if (TraceIsOn("bv2nat-check"))
      {
        Node x = i[0];

        Node valX = d_model.computeConcreteModelValue(x);

        Trace("bv2nat-check")
            << "* " << i << ", value = " << valBV2NatX << std::endl;
        Trace("bv2nat-check") << "  actual (" << valX  
                            << ") = " << valBV2NatxC << std::endl;
        // print the bit-vector versions
        Node bvalX = convertToBvK(k, valX);
        Node bvalBV2NatX = convertToBvK(k, valBV2NatX);
        Node bvalBV2NatXC = convertToBvK(k, valBV2NatXC);

        Trace("bv2nat-check") << "  bv-value = " << bvalBV2NatX << std::endl;
        Trace("bv2nat-check") << "  bv-actual (" << bvalX << ", " << bvalY
                            << ") = " << bvalBV2NatXC << std::endl;
      }
      if (valBV2NatX == valBV2NatXC)
      {
        Trace("bv2nat-check") << "...already correct" << std::endl;
        continue;
      }

        // this is the most naive model-based schema based on model values
        Node lem = valueBasedLemma(i);
        Trace("bv2nat-lemma")
            << "BV2NatSolver::Lemma: " << lem << " ; VALUE_REFINE" << std::endl;
        // send the value lemma
        d_im.addPendingLemma(lem,
                             InferenceId::ARITH_NL_BV2NAT_VALUE_REFINE,
                             nullptr,
                             true);
    }
  }
}

Node BV2NatSolver::convertToBvK(unsigned k, Node n) const
{
  Assert(n.isConst() && n.getType().isInteger());
  NodeManager* nm = nodeManager();
  Node iToBvOp = nm->mkConst(IntToBitVector(k));
  Node bn = nm->mkNode(Kind::INT_TO_BITVECTOR, iToBvOp, n);
  return rewrite(bn);
}

Node BV2NatSolver::valueBasedLemma(Node i)
{
  NodeManager* nm = nodeManager();
  Assert(i.getKind() == Kind::BITVECTOR_TO_NAT);
  Node x = i[0];

  uint32_t bvsize = x.getType().getBitVectorSize();
  Node twok = nm->mkConstInt(Rational(Integer(2).pow(bvsize)));
  Node valX = d_model.computeConcreteModelValue(x);
  valX = nm->mkNode(Kind::INTS_MODULUS, valX, twok);

  Node valC = nm->mkNode(Kind::BITVECTOR_TO_NAT, valX;
  valC = rewrite(valC);

  Node xm = nm->mkNode(Kind::INTS_MODULUS, x, twok);

  Node lem = nm->mkNode(Kind::IMPLIES,
                        nm->mkNode(xm.eqNode(valX),
                        i.eqNode(valC));
  return lem;
}


}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
