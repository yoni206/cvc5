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
#include "prop/prop_engine.h"
#include "prop/sat_solver.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace prop {

SatRelevancy::SatRelevancy(DPLLSatSolverInterface* satSolver,
                           context::Context* context,
                           CnfStream* cnfStream)
    : d_satSolver(satSolver),
      d_cnfStream(cnfStream),
      d_status(context),
      d_rlv(context)
{
}

SatRelevancy::~SatRelevancy() {}

void SatRelevancy::notifyPreprocessedAssertions(
    const std::vector<Node>& assertions)
{
  // mark everything as relevant
  for (const Node& a : assertions)
  {
    // notifyNewFormula(a);
    setRelevant(a, nullptr);
  }
}

void SatRelevancy::notifyNewLemma(TNode n, context::CDQueue<TNode>& queue) {}

void SatRelevancy::notifyAsserted(const SatLiteral& l,
                                  context::CDQueue<TNode>& queue)
{
  Node literalNode = d_cnfStream->getNode(l);
  if (!d_cnfStream->isNotifyFormula(literalNode))
  {
    // if relevant, enqueue
  }
}

void SatRelevancy::setRelevant(TNode n, context::CDQueue<TNode>* queue)
{
  context::CDHashSet<Node, NodeHashFunction>::iterator it = d_rlv.find(n);
  if (it != d_rlv.end())
  {
    // already marked relevant
    return;
  }
  d_rlv.insert(n);
  bool pol = n.getKind() != NOT;
  TNode atom = pol ? n : n[0];
  if (d_cnfStream->isNotifyFormula(n))
  {
    switch (atom.getKind())
    {
      case AND:
      case OR:
      {
        if (pol == (atom.getKind() == AND))
        {
          // all children are relevant
          for (const Node& ac : atom)
          {
            setRelevant(ac, queue);
          }
        }
        else
        {
          // The first asserted child is relevant. Maybe a child is already
          // asserted?
          bool waiting = true;
          bool value;
          for (const Node& ac : atom)
          {
            if (hasSatValue(ac, value))
            {
              if (value == pol)
              {
                setRelevant(ac, queue);
                waiting = false;
                break;
              }
            }
          }
          if (waiting)
          {
            // TODO
            for (const Node& ac : atom)
            {
            }
          }
        }
      }
      break;
      case ITE:
      {
        // mark the branch as relevant
        setRelevant(atom[0], queue);

        // Based on the asserted value of the condition, one branch becomes
        // relevant. Maybe the condition is already asserted?
        bool value;
        if (hasSatValue(atom[0], value))
        {
          setRelevant(atom[value ? 1 : 2]);
        }
        else
        {
          // TODO waiting for value
        }
      }
      break;
      case EQUAL:
      case XOR:
      {
        // mark children as relevant
        Assert(atom.getNumChildren() == 2);
        setRelevant(atom[0], queue);
        setRelevant(atom[1], queue);
      }
      break;
      default:
      {
        // should be a variable
        Assert(atom.isVar())
            << "SatRelevancy::setRelevant: unexpected notify formula " << n;
      }
      break;
    }
    return;
  }

  // otherwise it is a theory literal, if it has a SAT value, it should be
  // asserted
  if (hasSatValue(atom, value))
  {
    // now, enqueue it
    Assert(queue != nullptr);
    Node alit = value ? atom : atom.notNode();
    queue->push(alit);
  }
}

bool SatRelevancy::hasValue(TNode node, bool& value) const
{
  SatLiteral lit = d_cnfStream->getLiteral(node);
  SatValue v = d_satSolver->value(lit);
  if (v == SAT_VALUE_TRUE)
  {
    value = true;
    return true;
  }
  else if (v == SAT_VALUE_FALSE)
  {
    value = false;
    return true;
  }
  Assert(v == SAT_VALUE_UNKNOWN);
  return false;
}

}  // namespace prop
}  // namespace CVC4
