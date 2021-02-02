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

RlvProperty operator|(RlvProperty lhs, RlvProperty rhs)
{
  return static_cast<RlvProperty>(static_cast<uint32_t>(lhs)
                                  | static_cast<uint32_t>(rhs));
}
RlvProperty& operator|=(RlvProperty& lhs, RlvProperty rhs)
{
  lhs = lhs | rhs;
  return lhs;
}
RlvProperty operator&(RlvProperty lhs, RlvProperty rhs)
{
  return static_cast<RlvProperty>(static_cast<uint32_t>(lhs)
                                  & static_cast<uint32_t>(rhs));
}
RlvProperty& operator&=(RlvProperty& lhs, RlvProperty rhs)
{
  lhs = lhs & rhs;
  return lhs;
}

RlvInfo::RlvInfo(context::Context* context)
    : d_parents(context),
      d_parentPol(context),
      d_childPol(context),
      d_rlvp(context, RlvProperty::NONE)
{
}
bool RlvInfo::isRelevant(bool pol) const
{
  return (d_rlvp.get() & (pol ? RlvProperty::RLV_POS : RlvProperty::RLV_NEG))
         != RlvProperty::NONE;
}

void RlvInfo::setRelevant(bool pol)
{
  d_rlvp.set(d_rlvp.get()
             | (pol ? RlvProperty::RLV_POS : RlvProperty::RLV_NEG));
}

bool RlvInfo::isEnqueued() const
{
  return (d_rlvp.get() & RlvProperty::ENQUEUED) != RlvProperty::NONE;
}
void RlvInfo::setEnqueued()
{
  d_rlvp.set(d_rlvp.get() | RlvProperty::ENQUEUED);
}
bool RlvInfo::isJustified() const
{
  return (d_rlvp.get() & RlvProperty::JUSTIFIED) != RlvProperty::NONE;
}
void RlvInfo::setJustified()
{
  d_rlvp.set(d_rlvp.get() | RlvProperty::JUSTIFIED);
}
bool RlvInfo::isInput(bool& pol) const
{
  if ((d_rlvp.get() & RlvProperty::INPUT_POS) != RlvProperty::NONE)
  {
    pol = true;
    return true;
  }
  else 
  if ((d_rlvp.get() & RlvProperty::INPUT_NEG) != RlvProperty::NONE)
  {
    pol = false;
    return true;
  }
  return false;
}
void RlvInfo::setInput(bool pol) { d_rlvp.set(d_rlvp.get() | (pol ? RlvProperty::INPUT_POS : RlvProperty::INPUT_NEG)); }

SatRelevancy::SatRelevancy(CDCLTSatSolverInterface* satSolver,
                           context::Context* context,
                           context::UserContext* userContext,
                           CnfStream* cnfStream)
    : d_satSolver(satSolver),
      d_context(context),
      d_cnfStream(cnfStream),
      d_inputs(userContext),
      d_numInputs(context, 0),
      d_inputsRlv(context),
      d_rlvMap(context),
      d_numAsserts(context, 0),
      d_numAssertsRlv(context, 0)
{
  d_isActiveTmp = true;
}

SatRelevancy::~SatRelevancy() {}

void SatRelevancy::notifyAssertion(TNode a)
{
  // not used currently
  AlwaysAssert(false);
  /*
  // Mark each assertion as relevant. Notice we use a null queue since nothing
  // should have SAT values yet.
  Trace("sat-rlv") << "notifyAssertion: " << a << std::endl;
  //Assert(d_inputs.size() == d_inputsRlv.size());
  d_inputs.push_back(a);
  //d_inputsRlv.insert(a);
  d_numInputs = d_numInputs + 1;
  setRelevant(a, true, nullptr);
  */
}

void SatRelevancy::notifyLemma(TNode lem, context::CDQueue<TNode>& queue)
{
  // relevancy is SAT-context dependent, need to double check lemmas
  // when we backtrack
  Trace("sat-rlv") << "notifyLemma: " << lem << std::endl;
  d_inputs.push_back(lem);
  Trace("sat-rlv") << "notifyLemma: finished" << std::endl;
}

void SatRelevancy::notifyActivatedSkolemDef(TNode n,
                                            context::CDQueue<TNode>& queue)
{
  Trace("sat-rlv") << "notifyActivatedSkolemDef: " << n << std::endl;
  // set the lemma is currently relevant
  setRelevant(n, true, &queue);
  Trace("sat-rlv") << "notifyActivatedSkolemDef: finished" << std::endl;
}

void SatRelevancy::notifyDecisionRequest(TNode n,
                                         context::CDQueue<TNode>& queue)
{
  Trace("sat-rlv") << "notifyActivatedSkolemDef: " << n << std::endl;
  // set the lemma is currently relevant
  setRelevant(n, true, &queue);
  Trace("sat-rlv") << "notifyActivatedSkolemDef: finished" << std::endl;
}

void SatRelevancy::notifyAsserted(const SatLiteral& l,
                                  context::CDQueue<TNode>& queue)
{
  TNode n = d_cnfStream->getNode(l);
  Trace("sat-rlv") << "notifyAsserted: " << n << std::endl;
  if (!d_isActiveTmp)
  {
    queue.push(n);
  }
  bool pol = n.getKind() != NOT;
  TNode atom = pol ? n : n[0];
  bool nrlv = false;
  // first, look at wait lists
  RlvInfo* ri = getOrMkRlvInfo(atom);
    // we are going to iterate through each parent that is waiting
    // on its value and possibly update relevancy
    Assert(ri->d_parents.size() == ri->d_childPol.size());
    for (size_t i = 0, nparents = ri->d_parents.size(); i < nparents; i++)
    {
      TNode parent = ri->d_parents[i];
      bool ppol = ri->d_parentPol[i];
      bool cpol = ri->d_childPol[i];
      Trace("sat-rlv-debug")
          << "  look at parent: " << parent << ", cpol=" << cpol << std::endl;
      // n makes a child of parent have value equal to (pol==cpol), where pol
      // is the assigned value of the atom, and cpol is its polarity in the
      // parent. For instance, (and (not A) B), when A is assigned true, we
      // get that pol=true, cpol = false, and hence we notify that a child of
      // AND is false.
      if (setAssertedChild(atom, pol == cpol, parent, ppol, queue))
      {
        Trace("sat-rlv-debug") << "  ...now relevant" << std::endl;
        // due to the above call, n is now relevant
        nrlv = true;
      }
    }
  
  // note that notify formulas are in terms of atoms
  if (!d_cnfStream->isNotifyFormula(atom))
  {
    d_numAsserts.set(d_numAsserts + 1);
    // we are a theory literal
    // if we became relevant due to a parent, or are already relevant, enqueue
    if (nrlv || ri->isRelevant(pol))
    {
      if (!ri->isEnqueued())
      {
        Trace("sat-rlv") << "*** enqueue from assert " << n << std::endl;
        if (d_isActiveTmp)
        {
          queue.push(n);
        }
        //d_enqueued.insert(atom);
        ri->setEnqueued();
        d_numAssertsRlv.set(d_numAssertsRlv + 1);
      }
    }
    // otherwise we will assert if the literal gets marked as relevant
  }
  else if (nrlv)
  {
    // based on parents, this formula is now relevant and is not a theory atom
    setRelevantInternal(atom, pol, &queue);
  }
  Trace("sat-rlv") << "notifyAsserted: finished" << std::endl;
}

void SatRelevancy::setRelevant(TNode n,
                               bool pol,
                               context::CDQueue<TNode>* queue,
                               bool input)
{
  if (n.getKind() == NOT)
  {
    pol = !pol;
    n = n[0];
  }
  setRelevantInternal(n, pol, queue, input);
}

void SatRelevancy::setRelevantInternal(TNode atom,
                                       bool pol,
                                       context::CDQueue<TNode>* queue,
                                       bool input)
{
  RlvInfo* ri = getOrMkRlvInfo(atom);
  if (ri->isRelevant(pol))
  {
    // already marked relevant
    return;
  }
  Trace("sat-rlv") << "- set relevant: " << atom << ", pol = " << pol
                   << std::endl;
  ri->setRelevant(pol);
  Assert(atom.getKind() != NOT);
  // notify formulas are in terms of atoms
  // NOTE this could be avoided by simply looking at the kind?
  Trace("sat-rlv-debug") << "  notifyFormula: "
                         << d_cnfStream->isNotifyFormula(atom) << std::endl;
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
          for (TNode ac : atom)
          {
            setRelevant(ac, pol, queue);
          }
        }
        else
        {
          // The first asserted child is relevant. Maybe a child is already
          // asserted?
          bool justified = false;
          bool value;
          std::vector<TNode> acb;
          for (TNode ac : atom)
          {
            if (hasSatValue(ac, value))
            {
              if (value == pol)
              {
                // the value of the child justifies the node, we mark it as
                // relevant and are done. Notice the polarity (pol) is important
                //   ac = false justifies an AND parent being false,
                //   ac = true justifies an OR parent being true.
                Trace("sat-rlv-debug")
                    << "  ...justified already by " << ac << std::endl;
                setRelevant(ac, pol, queue);
                justified = true;
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
          if (!justified)
          {
            // for all children that do not yet have values
            for (TNode ac : acb)
            {
              addParentRlvWait(ac, true, atom, pol);
            }
          }
        }
      }
      break;
      case IMPLIES:
      {
        if (!pol)
        {
          // children are immediately relevant
          setRelevant(atom[0], true, queue);
          setRelevant(atom[1], false, queue);
        }
        else
        {
          // The first asserted child is relevant. Maybe a child is already
          // asserted?
          bool justified = false;
          bool value;
          std::vector<TNode> acb;
          std::vector<size_t> acbi;
          for (size_t i = 0; i < 2; i++)
          {
            TNode ac = atom[i];
            if (hasSatValue(ac, value))
            {
              // does the child make the IMPLIES true?
              if (value == (i == 1))
              {
                Trace("sat-rlv-debug")
                    << "  ...justified already by " << ac << std::endl;
                setRelevant(ac, value, queue);
                justified = true;
                break;
              }
            }
            else
            {
              acb.push_back(ac);
              acbi.push_back(i);
            }
          }
          // no children are asserted with the desired value, we are waiting for
          // the values for those that do no yet have values
          if (!justified)
          {
            // for all children that do not yet have values
            for (size_t i = 0, acbs = acb.size(); i < acbs; i++)
            {
              addParentRlvWait(acb[i], acbi[i] == 1, atom, pol);
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
        Assert(atom[0].getKind() != NOT);
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
          addParentRlvWait(atom[0], true, atom, pol);
        }
      }
      break;
      case EQUAL:
      case XOR:
      {
        Assert(atom.getNumChildren() == 2);
        // notify formulas of kind EQUAL should only be Boolean (IFF)
        Assert(atom[0].getType().isBoolean());
        // do we have values for either of the children?
        bool value;
        if (hasSatValue(atom[0], value))
        {
          setRelevant(atom[0], value, queue);
          // atom[1] is also relevant with the proper polarity
          setRelevant(
              atom[1], value == (pol == (atom.getKind() == EQUAL)), queue);
        }
        else if (hasSatValue(atom[1], value))
        {
          setRelevant(atom[1], value, queue);
          // atom[0] is also relevant with the proper polarity
          setRelevant(
              atom[0], value == (pol == (atom.getKind() == EQUAL)), queue);
        }
        else
        {
          // neither have values, we are waiting
          for (size_t i = 0; i < 2; i++)
          {
            addParentRlvWait(atom[i], true, atom, pol);
          }
        }
      }
      break;
      default:
      {
        // should be a variable
        Assert(atom.isVar())
            << "SatRelevancy::setRelevant: unexpected notify formula " << atom;
      }
      break;
    }
    return;
  }
  // if there is no queue, we are asserting that an input assertion is relevant,
  // it will be asserted anyways.
  Assert(queue != nullptr);
  // otherwise it is a theory literal, if it already has a SAT value, it should
  // be asserted now
  bool hasValue;
  bool value;
  if (input)
  {
    ri->setInput(pol);
    value = pol;
    hasValue = true;
  }
  else if (ri->isInput(value))
  {
    hasValue = true;
  }
  else
  {
    hasValue = hasSatValue(atom, value);
  }
  // special case for top-level assertions, which may not have literals since
  // CNF does not introduce intermediate literals for some top-level formulas
  if (hasValue)
  {
    // now, enqueue it
    if (!ri->isEnqueued())
    {
      Node alit = value ? Node(atom) : atom.notNode();
      Trace("sat-rlv") << "*** enqueue " << alit << std::endl;
      if (d_isActiveTmp)
      {
        queue->push(alit);
      }
      ri->setEnqueued();
      d_numAssertsRlv.set(d_numAssertsRlv + 1);
    }
  }
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

void SatRelevancy::addParentRlvWait(TNode n,
                                    bool pol,
                                    TNode parentAtom,
                                    bool ppol)
{
  if (n.getKind() == NOT)
  {
    pol = !pol;
    n = n[0];
  }
  RlvInfo* rwi = getOrMkRlvInfo(n);
  rwi->d_parents.push_back(parentAtom);
  rwi->d_parentPol.push_back(ppol);
  rwi->d_childPol.push_back(pol);
  Trace("sat-rlv-debug") << "  ...add parent rlv wait: " << n << " -> "
                         << parentAtom << ", ppol=" << ppol << std::endl;
}
RlvInfo* SatRelevancy::getOrMkRlvInfo(TNode n)
{
  RlvMap::const_iterator it = d_rlvMap.find(n);
  if (it != d_rlvMap.end())
  {
    return it->second.get();
  }
  std::shared_ptr<RlvInfo> rwi = std::make_shared<RlvInfo>(d_context);
  d_rlvMap.insert(n, rwi);
  return rwi.get();
}

bool SatRelevancy::setAssertedChild(TNode atom,
                                    bool pol,
                                    TNode parentAtom,
                                    bool ppol,
                                    context::CDQueue<TNode>& queue)
{
  Trace("sat-rlv-debug") << "setAssertedChild " << pol << " in " << parentAtom
                         << " with ppol=" << ppol << ", from " << atom
                         << std::endl;
  switch (parentAtom.getKind())
  {
    case AND:
    case OR:
    case IMPLIES:
    {
      Assert(ppol == (parentAtom.getKind() != AND));
      RlvInfo* pri = getOrMkRlvInfo(parentAtom);
      if (pri->isJustified())
      {
        Trace("sat-rlv-debug") << "...already justified" << std::endl;
        // the parent was already justified by another child, nothing to do
        return false;
      }
      // does it make the parent true?
      if (pol == ppol)
      {
        Trace("sat-rlv-debug") << "...now justified" << std::endl;
        // we've justified the parent
        pri->setJustified();
        // the value of this is relevant
        return true;
      }
      // otherwise the value of this is not relevant
    }
    break;
    case ITE:
    {
      // now set the proper branch to be relevant with the parent's polarity
      setRelevant(parentAtom[pol ? 1 : 2], ppol, &queue);
      // the value of this is now also relevant
      return true;
    }
    break;
    case EQUAL:
    case XOR:
    {
      // the value of the other side is now relevant
      for (size_t i = 0; i < 2; i++)
      {
        TNode pc = parentAtom[i];
        TNode pcatom = pc.getKind() == NOT ? pc[0] : pc;
        if (pcatom == atom)
        {
          setRelevant(parentAtom[1 - i],
                      pol == (ppol == (parentAtom.getKind() == EQUAL)),
                      &queue);
          break;
        }
      }
      // the value of this is now also relevant
      return true;
    }
    break;
    default:
    {
      Unhandled()
          << "SatRelevancy::setAssertedChild: unexpected parent formula "
          << parentAtom;
    }
    break;
  }
  return false;
}

void SatRelevancy::ensureLemmasRelevant(context::CDQueue<TNode>* queue)
{
  size_t index = d_numInputs.get();
  size_t numInputs = d_inputs.size();
  if (index >= numInputs)
  {
    return;
  }
  Trace("sat-rlv") << "ensureLemmasRelevant" << std::endl;
  while (index < numInputs)
  {
    TNode lem = d_inputs[index];
    Trace("sat-rlv") << "ensureLemmaRelevant: " << lem << std::endl;
    setRelevant(lem, true, queue, true);
    index++;
  }
  Trace("sat-rlv") << "...finished ensureLemmasRelevant" << std::endl;
  d_numInputs = numInputs;
}

void SatRelevancy::check(theory::Theory::Effort effort,
                         context::CDQueue<TNode>& queue)
{
  ensureLemmasRelevant(&queue);
  if (Trace.isOn("sat-rlv-summary"))
  {
    if (theory::Theory::fullEffort(effort))
    {
      Trace("sat-rlv-summary")
          << "SatRelevancy::check(" << effort << "): " << d_numAssertsRlv.get()
          << "/" << d_numAsserts.get() << " assertions relevant" << std::endl;
    }
  }
}

}  // namespace prop
}  // namespace CVC4
