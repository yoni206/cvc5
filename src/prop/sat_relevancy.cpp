/*********************                                                        */
/*! \file sat_relevancy.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Sat relevancy module
 **/

#include "prop/sat_relevancy.h"

#include "prop/cnf_stream.h"

namespace CVC4 {
namespace prop {

SatRelevancy::SatRelevancy(context::Context* context, CnfStream* cnfStream) : d_cnfStream(cnfStream), d_status(context) {}

SatRelevancy::~SatRelevancy() {}

void SatRelevancy::notifyPreprocessedAssertions(const std::vector<Node>& assertions)
{
  // mark everything as relevant
  for (const Node& a : assertions)
  {
    //notifyNewFormula(a);
  }
}

void SatRelevancy::notifyNewLemma(TNode n, context::CDQueue<TNode>& queue)
{
}

void SatRelevancy::notifyAsserted(const SatLiteral& l,
                                         context::CDQueue<TNode>& queue)
{
  Node literalNode = d_cnfStream->getNode(l);
  if (!d_cnfStream->isNotifyFormula(literalNode))
  {
    // updates relevancy
  }
  else
  {
    // if also relevant, 
  }
}

void SatRelevancy::setRelevant(TNode n, context::CDQueue<TNode>& queue)
{
  
}


}  // namespace prop
}  // namespace CVC4
