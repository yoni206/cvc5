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
      d_context(context),
      d_cnfStream(cnfStream),
      d_rlv(context),
      d_rlvWaitMap(context)
{
}

SatRelevancy::~SatRelevancy() {}

void SatRelevancy::notifyPreprocessedAssertions(
    const std::vector<Node>& assertions)
{
  // Mark each assertion as relevant. Notice we use a null queue since nothing
  // should have SAT values yet.
  for (const Node& a : assertions)
  {
    setRelevant(a, nullptr);
  }
}

void SatRelevancy::notifyNewLemma(TNode n, context::CDQueue<TNode>& queue) 
{
  // set the lemma is relevant
  setRelevant(n, &queue);
}

void SatRelevancy::notifyAsserted(const SatLiteral& l,
                                  context::CDQueue<TNode>& queue)
{
  Node n = d_cnfStream->getNode(l);
  bool pol = n.getKind() != NOT;
  TNode atom = pol ? n : n[0];
  // notify formulas are in terms of atoms
  if (!d_cnfStream->isNotifyFormula(atom))
  {
    // if already relevant, enqueue
    if (d_rlv.find(n)!=d_rlv.end())
    {
      queue.push(n);
    }
    // otherwise we will assert if the literal gets marked as relevant
  }
  // now, look at wait lists
  RlvWaitMap::const_iterator it = d_rlvWaitMap.find(atom);
  if (it==d_rlvWaitMap.end())
  {
    // nothing is waiting on its value, we are done.
    return;
  }
  // otherwise, we are going to iterate through each parent that is waiting
  // on its value and possibly update relevancy
  RlvWaitInfo * rwi = it->second.get();
  for (const Node& parent : rwi->d_parents)
  {
    setAssertedChild(atom, pol, parent, queue);
  }
}

void SatRelevancy::setRelevant(TNode n, context::CDQueue<TNode>* queue)
{
  if (d_rlv.find(n) != d_rlv.end())
  {
    // already marked relevant
    return;
  }
  Trace("sat-rlv") << "Set relevant: " << n << std::endl;
  d_rlv.insert(n);
  bool pol = n.getKind() != NOT;
  TNode atom = pol ? n : n[0];
  Assert (atom.getKind()!=NOT);
  // notify formulas are in terms of atoms
  // NOTE this could be avoided by simply looking at the kind?
  if (d_cnfStream->isNotifyFormula(atom))
  {
    switch (atom.getKind())
    {
      case AND:
      case OR:
      {
        if (pol == (atom.getKind() == AND))
        {
          // all children are immediately relevant
          for (const Node& ac : atom)
          {
            setRelevant(ac, pol, queue);
          }
        }
        else
        {
          // The first asserted child is relevant. Maybe a child is already
          // asserted?
          bool waiting = true;
          bool value;
          std::vector<Node> acb;
          for (const Node& ac : atom)
          {
            if (hasSatValue(ac, value))
            {
              if (value == pol)
              {
                // the value of the child justifies the node, we mark it as
                // relevant and are done. Notice the polarity (pol) is important
                //   ac = false justifies an AND parent being false,
                //   ac = true justifies an OR parent being true.
                setRelevant(ac, pol, queue);
                waiting = false;
                break;
              }
            }
            else
            {
              acb.push_back(ac);
            }
          }
          // no children are asserted with the desired value, we are waiting for
          // the values for those that do no yet have values
          if (waiting)
          {
            // for all children that do not yet have values
            for (const Node& ac : acb)
            {
              RlvWaitInfo * rwi = getOrMkRlvWaitInfo(ac);
              rwi->d_parents.push_back(n);
            }
          }
        }
      }
      break;
      case ITE:
      {
        // Based on the asserted value of the condition, one branch becomes
        // relevant. Maybe the condition is already asserted?
        bool value;
        if (hasSatValue(atom[0], value))
        {
          // the condition's value is relevant
          setRelevant(atom[0], value, queue);
          // the proper branch, with the proper polarity, is also relevant
          setRelevant(atom[value ? 1 : 2], pol, queue);
        }
        else
        {
          // otherwise, we are waiting for the value of the condition
          RlvWaitInfo * rwi = getOrMkRlvWaitInfo(atom[0]);
          rwi->d_parents.push_back(n);
        }
      }
      break;
      case EQUAL:
      case XOR:
      {
        Assert(atom.getNumChildren() == 2);
        // do we have values for either of the children?
        bool value;
        if (hasSatValue(atom[0], value))
        {
          setRelevant(atom[0], value, queue);
          // atom[1] is also relevant with the proper polarity
          setRelevant(atom[1], value==pol, queue);
        }
        else if (hasSatValue(atom[1], value))
        {
          setRelevant(atom[1], value, queue);
          // atom[0] is also relevant with the proper polarity
          setRelevant(atom[0], value==pol, queue);
        }
        else
        {
          // neither have values, we are waiting
          for (size_t i=0; i<2; i++)
          {
            RlvWaitInfo * rwi = getOrMkRlvWaitInfo(atom[i]);
            rwi->d_parents.push_back(n);
          }
        }
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

  // otherwise it is a theory literal, if it already has a SAT value, it should
  // be asserted now
  bool value;
  if (hasSatValue(atom, value))
  {
    // now, enqueue it
    Assert(queue != nullptr);
    Node alit = value ? Node(atom) : atom.notNode();
    queue->push(alit);
  }
}

void SatRelevancy::setRelevant(TNode n, bool pol, context::CDQueue<TNode>* queue)
{
  Node np = pol ? Node(n) : n.negate();
  setRelevant(np, queue);
}

bool SatRelevancy::hasSatValue(TNode node, bool& value) const
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

RlvWaitInfo * SatRelevancy::getOrMkRlvWaitInfo(TNode n)
{
  TNode atom = n.getKind()==NOT ? n[0] : n;
  RlvWaitMap::const_iterator it = d_rlvWaitMap.find(atom);
  if (it!=d_rlvWaitMap.end())
  {
    return it->second.get();
  }
  std::shared_ptr<RlvWaitInfo> rwi = std::make_shared<RlvWaitInfo>(d_context);
  d_rlvWaitMap.insert(atom, rwi);
  return rwi.get();
}

void SatRelevancy::setAssertedChild(TNode atom, bool pol, Node parent, context::CDQueue<TNode>& queue)
{
  // TODO
}

}  // namespace prop
}  // namespace CVC4
