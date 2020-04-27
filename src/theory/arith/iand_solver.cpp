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
      d_model(model)
{
  NodeManager* nm = NodeManager::currentNM();
  d_true = nm->mkConst(true);
  d_false = nm->mkConst(false);
  d_zero = nm->mkConst(Rational(0));
  d_one = nm->mkConst(Rational(1));
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

}  // namespace arith
}  // namespace theory
}  // namespace CVC4
