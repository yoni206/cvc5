/*********************                                                        */
/*! \file iand_solver.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of integer and (IAND) solver
 **/

#include "theory/arith/iand_solver.h"

#include "options/arith_options.h"
#include "theory/arith/arith_msum.h"
#include "theory/arith/arith_utilities.h"
#include "util/iand.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace arith {

IAndSolver::IAndSolver(TheoryArith& containing, NlModel& model)
    : d_containing(containing),
      d_model(model),
      d_initRefine(containing.getUserContext())
{
  NodeManager* nm = NodeManager::currentNM();
  d_true = nm->mkConst(true);
  d_false = nm->mkConst(false);
  d_zero = nm->mkConst(Rational(0));
  d_one = nm->mkConst(Rational(1));
  d_two = nm->mkConst(Rational(2));
  d_neg_one = nm->mkConst(Rational(-1));
}

IAndSolver::~IAndSolver() {}

void IAndSolver::initLastCall(const std::vector<Node>& assertions,
                              const std::vector<Node>& false_asserts,
                              const std::vector<Node>& xts)
{
  d_iands.clear();

  Trace("iand-mv") << "IAND terms : " << std::endl;
  for (const Node& a : xts)
  {
    Kind ak = a.getKind();
    if (ak == IAND)
    {
      size_t bsize = a.getOperator().getConst<IntAnd>().d_size;
      d_iands[bsize].push_back(a);
    }
  }

  Trace("iand") << "We have " << d_iands.size() << " IAND terms." << std::endl;
}

std::vector<Node> IAndSolver::checkInitialRefine()
{
  Trace("iand-check") << "IAndSolver::checkInitialRefine" << std::endl;
  std::vector<Node> lems;
  NodeManager* nm = NodeManager::currentNM();
  for (const std::pair<const unsigned, std::vector<Node> >& is : d_iands)
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
      // initial refinement lemmas
      std::vector<Node> conj;
      // 0 <= iand(x,y) < 2^k
      conj.push_back(nm->mkNode(LEQ,d_zero,i));
      conj.push_back(nm->mkNode(LT,i,nm->mkNode(POW,d_two,nm->mkConst(Rational(k)))));
      // iand(x,y)=iand(y,x)
      conj.push_back(i.eqNode(nm->mkNode(IAND, op, i[1], i[0])));
      // iand(x,y)<=x
      conj.push_back(nm->mkNode(LEQ, i, i[0]));
      // iand(x,y)<=y
      conj.push_back(nm->mkNode(LEQ, i, i[1]));
      // x=y => iand(x,y)=x
      conj.push_back(nm->mkNode(IMPLIES,i[0].eqNode(i[1]), i.eqNode(i[0])));

      Assert(conj.size() > 1);
      Node lem = nm->mkNode(AND, conj);
      Trace("iand-lemma") << "IAndSolver::checkInitialRefine: " << i << " : "
                          << lem << std::endl;
      lems.push_back(lem);
    }
  }
  return lems;
}

std::vector<Node> IAndSolver::checkFullRefine()
{
  Trace("iand-check") << "IAndSolver::checkFullRefine";
  Trace("iand-check") << "IAND terms: " << std::endl;
  std::vector<Node> lems;
  NodeManager* nm = NodeManager::currentNM();
  for (const std::pair<const unsigned, std::vector<Node> >& is : d_iands)
  {
    // the reference bitwidth
    unsigned k = is.first;
    for (const Node& i : is.second)
    {
      Node x = i[0];
      Node y = i[1];

      Node valX = d_model.computeConcreteModelValue(x);
      Node valY = d_model.computeConcreteModelValue(y);
      Node valAndXY = d_model.computeAbstractModelValue(i);
      Node valAndXYC = d_model.computeConcreteModelValue(i);

      if (Trace.isOn("iand-check"))
      {
        Trace("iand-check")
            << "* " << i << ", value = " << valAndXY << std::endl;
        Trace("iand-check") << "  actual (" << valX << ", " << valY
                            << ") = " << valAndXYC << std::endl;
        // print the bit-vector versions
        Node bvalX = convertToBvK(k, valX);
        Node bvalY = convertToBvK(k, valY);
        Node bvalAndXY = convertToBvK(k, valAndXY);
        Node bvalAndXYC = convertToBvK(k, valAndXYC);

        Trace("iand-check")
            << "  bvalue = " << bvalAndXY << std::endl;
        Trace("iand-check") << "  actual (" << bvalX << ", " << bvalY
                            << ") = " << bvalAndXYC << std::endl;
      }

      // additional axioms go here
    }
  }

  return lems;
}

Node IAndSolver::convertToBvK(unsigned k, Node n)
{
  Assert (n.isConst() && n.getType().isInteger());
  NodeManager * nm = NodeManager::currentNM();
  Node iToBvop = nm->mkConst(IntToBitVector(k));
  Node bn = nm->mkNode(kind::INT_TO_BITVECTOR, iToBvop, n);
  return Rewriter::rewrite(bn);
}

}  // namespace arith
}  // namespace theory
}  // namespace CVC4
