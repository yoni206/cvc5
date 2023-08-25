/******************************************************************************
 * Top contributors (to current version):
 *   Hans-Jörg Schurr
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The printer for the experimental AletheLF format.
 */

#include "proof/alf/alf_printer.h"

#include <cctype>
#include <iostream>
#include <memory>
#include <ostream>
#include <sstream>

#include "expr/node_algorithm.h"
#include "printer/printer.h"
#include "proof/alf/alf_proof_rule.h"
#include "proof/proof_node_to_sexpr.h"
#include "smt/print_benchmark.h"

namespace cvc5::internal {

namespace proof {

AlfPrinter::AlfPrinter() {}

std::string AlfPrinter::getRuleName(const ProofNode* pfn)
{
  std::string name;
  if (pfn->getRule() == PfRule::ALF_RULE)
  {
    name = aletheLFRuleToString(getAletheLFRule(pfn->getArguments()[0]));
  }
  else
  {
    name = toString(pfn->getRule());
  }
  std::transform(name.begin(), name.end(), name.begin(), [](unsigned char c) {
    return std::tolower(c);
  });
  return name;
}

void AlfPrinter::printOrdinaryStep(
    std::ostream& out,
    std::shared_ptr<ProofNode> pfn,
    const size_t& lastStep,
    std::map<std::shared_ptr<ProofNode>, size_t>& stepMap)
{
  out << "(step t" << lastStep << " " << pfn->getResult() << " :rule "
      << getRuleName(pfn.get());

  if (pfn->getChildren().size() == 0 && pfn->getArguments().size() > 0)
  {
    out << " :premises ()";
  }
  else if (pfn->getChildren().size() > 0)
  {
    bool first = true;
    for (std::shared_ptr<ProofNode> premise : pfn->getChildren())
    {
      if (first)
      {
        out << " :premises (";
        first = false;
      }
      else
      {
        out << " ";
      }
      out << "t" << stepMap[premise];
    }
    out << ")";
  }
  if ((pfn->getRule() == PfRule::ALF_RULE && pfn->getArguments().size() > 1)
      || (pfn->getRule() != PfRule::ALF_RULE && pfn->getArguments().size() > 0))
  {
    // Hack to get the arguments converted into something useful
    ProofNodeToSExpr sexpPrinter;
    Node sexp = sexpPrinter.convertToSExpr(pfn.get(), false);
    bool first = true;
    // this is a problem
    bool skipFirst = (pfn->getRule() == PfRule::ALF_RULE);
    for (Node arg : sexp[sexp.getNumChildren() - 1])
    {
      if (skipFirst)
      {
        skipFirst = false;
        continue;
      }
      if (first)
      {
        out << " :args (";
        first = false;
      }
      else
      {
        out << " ";
      }
      out << arg;
    }
    out << ")";
  }
  out << ")" << std::endl;
}

void AlfPrinter::printProof(
    std::ostream& out,
    std::shared_ptr<ProofNode> pfn,
    size_t& lastStep,
    std::map<std::shared_ptr<ProofNode>, size_t>& stepMap)
{
  if (pfn->getRule() == PfRule::SCOPE)
  {
    out << "; Oh no! it's a scope." << std::endl;
  }

  const std::vector<std::shared_ptr<ProofNode>>& children = pfn->getChildren();
  for (const std::shared_ptr<ProofNode>& ch : children)
  {
    printProof(out, ch, lastStep, stepMap);
  }

  switch (pfn->getRule())
  {
    case PfRule::SCOPE: return;
    case PfRule::ASSUME:
      out << "(assume t" << lastStep << " " << pfn->getResult() << ")"
          << std::endl;
      break;
    default: printOrdinaryStep(out, pfn, lastStep, stepMap); break;
  }
  stepMap[pfn] = lastStep;
  lastStep += 1;
}

void AlfPrinter::print(std::ostream& out, std::shared_ptr<ProofNode> pfn)
{
  d_pfIdCounter = 0;

  // [1] Get the definitions and assertions and print the declarations from them
  const std::vector<Node>& definitions = pfn->getArguments();
  const std::vector<Node>& assertions = pfn->getChildren()[0]->getArguments();
  const ProofNode* pnBody = pfn->getChildren()[0]->getChildren()[0].get();

  // TODO: preprocess definitions/assertions with the term converter
  smt::PrintBenchmark pb(Printer::getPrinter(out));
  pb.printDeclarationsFrom(out, definitions, assertions);

  LetBinding lbind;
  AlfPrintChannelPre aletify(lbind);
  AlfPrintChannelOut aprint(out);

  std::map<const ProofNode*, size_t> pletMap;
  std::map<Node, size_t> passumeMap;

  // [2] print assumptions
  bool wasAlloc;
  for (size_t i = 0; i < 2; i++)
  {
    AlfPrintChannel* aout;
    if (i == 0)
    {
      aout = &aletify;
    }
    else
    {
      aout = &aprint;
    }
    // TODO: not necessary
    for (const Node& n : definitions)
    {
      size_t id = allocateAssumeId(n, passumeMap, wasAlloc);
      aout->printAssume(n, id, false);
    }
    for (const Node& n : assertions)
    {
      size_t id = allocateAssumeId(n, passumeMap, wasAlloc);
      aout->printAssume(n, id, false);
    }
    printProofInternal(aout, pnBody, lbind, pletMap, passumeMap);
  }
  // outer method to print valid AletheLF output from a ProofNode
  std::map<std::shared_ptr<ProofNode>, size_t> stepMap;
  size_t lastStep;
  printProof(out, pfn, lastStep, stepMap);
  out << "\n";
}

void AlfPrinter::printProofInternal(AlfPrintChannel* out,
                                    const ProofNode* pn,
                                    const LetBinding& lbind,
                                    std::map<const ProofNode*, size_t>& pletMap,
                                    std::map<Node, size_t>& passumeMap)
{
  // the stack
  std::vector<const ProofNode*> visit;
  // whether we have to process children
  std::unordered_map<const ProofNode*, bool> processingChildren;
  // helper iterators
  std::unordered_map<const ProofNode*, bool>::iterator pit;
  const ProofNode* cur;
  visit.push_back(pn);
  do
  {
    cur = visit.back();
    pit = processingChildren.find(cur);
    if (pit == processingChildren.end())
    {
      PfRule r = cur->getRule();
      if (r == PfRule::ASSUME)
      {
        // ignore
        visit.pop_back();
        continue;
      }
      else if (r == PfRule::ENCODE_PRED_TRANSFORM)
      {
        // just add child
        visit.pop_back();
        visit.push_back(cur->getChildren()[0].get());
        continue;
      }
      printStepPre(out, cur, lbind, pletMap, passumeMap);
      // a normal rule application, compute the proof arguments, which
      // notice in the case of PI also may modify our passumeMap.
      processingChildren[cur] = true;
      // will revisit this proof node
      const std::vector<std::shared_ptr<ProofNode>>& children =
          cur->getChildren();
      // visit each child
      for (const std::shared_ptr<ProofNode>& c : children)
      {
        visit.push_back(c.get());
      }
      continue;
    }
    visit.pop_back();
    if (pit->second)
    {
      processingChildren[cur] = false;
      printStepPost(out, cur, lbind, pletMap, passumeMap);
    }
  } while (!visit.empty());
}

void AlfPrinter::printStepPre(AlfPrintChannel* out,
                              const ProofNode* pn,
                              const LetBinding& lbind,
                              std::map<const ProofNode*, size_t>& pletMap,
                              std::map<Node, size_t>& passumeMap)
{
  // if we haven't yet allocated a proof id, do it now
  PfRule r = pn->getRule();
  if (r == PfRule::ALF_RULE)
  {
    Assert(!pn->getArguments().empty());
    Node rn = pn->getArguments()[0];
    AletheLFRule ar = getAletheLFRule(rn);
    if (ar == AletheLFRule::SCOPE)
    {
      Assert(pn->getArguments().size() == 2);
      Node a = pn->getArguments()[1];
      bool wasAlloc = false;
      size_t aid = allocateAssumeId(a, passumeMap, wasAlloc);
      // if we assigned an id to the assumption,
      if (wasAlloc)
      {
        d_activeScopes.insert(pn);
      }
      else
      {
        // otherwise we shadow, just use a dummy
        d_pfIdCounter++;
        aid = d_pfIdCounter;
      }
      // print a push
      out->printAssume(a, aid, true);
    }
  }
}
void AlfPrinter::printStepPost(AlfPrintChannel* out,
                               const ProofNode* pn,
                               const LetBinding& lbind,
                               std::map<const ProofNode*, size_t>& pletMap,
                               std::map<Node, size_t>& passumeMap)
{
  // if we have yet to allocate a proof id, do it now
  bool wasAlloc = false;
  size_t id = allocateProofId(pn, pletMap, wasAlloc);
  bool isPop = false;
  PfRule r = pn->getRule();
  std::vector<Node> args;
  if (r == PfRule::ALF_RULE)
  {
    Node rn = pn->getArguments()[0];
    AletheLFRule ar = getAletheLFRule(rn);
    // if scope, do pop the assumption from passumeMap
    if (ar == AletheLFRule::SCOPE)
    {
      isPop = true;
      if (d_activeScopes.find(pn) != d_activeScopes.end())
      {
        Node a = pn->getArguments()[1];
        passumeMap.erase(a);
      }
    }
    const std::vector<Node> aargs = pn->getArguments();
    args.insert(args.end(), aargs.begin() + 1, aargs.end());
  }
  else
  {
    args = pn->getArguments();
  }
  TNode conclusion = pn->getResult();
  std::vector<size_t> premises;
  const std::vector<std::shared_ptr<ProofNode>>& children = pn->getChildren();
  std::map<Node, size_t>::iterator ita;
  std::map<const ProofNode*, size_t>::iterator itp;
  for (const std::shared_ptr<ProofNode>& c : children)
  {
    size_t pid;
    if (c->getRule() == PfRule::ASSUME)
    {
      ita = passumeMap.find(c->getResult());
      Assert(ita != passumeMap.end());
      pid = ita->second;
    }
    else
    {
      itp = pletMap.find(c.get());
      Assert(itp != pletMap.end());
      pid = itp->second;
    }
    premises.push_back(pid);
  }
  std::string rname = getRuleName(pn);
  out->printStep(rname, conclusion, id, premises, args, isPop);
}

size_t AlfPrinter::allocateAssumeId(const Node& n,
                                    std::map<Node, size_t>& passumeMap,
                                    bool& wasAlloc)
{
  std::map<Node, size_t>::iterator it = passumeMap.find(n);
  if (it != passumeMap.end())
  {
    wasAlloc = false;
    return it->second;
  }
  wasAlloc = true;
  d_pfIdCounter++;
  passumeMap[n] = d_pfIdCounter;
  return d_pfIdCounter;
}

size_t AlfPrinter::allocateProofId(const ProofNode* pn,
                                   std::map<const ProofNode*, size_t>& pletMap,
                                   bool& wasAlloc)
{
  std::map<const ProofNode*, size_t>::iterator it = pletMap.find(pn);
  if (it != pletMap.end())
  {
    wasAlloc = false;
    return it->second;
  }
  wasAlloc = true;
  d_pfIdCounter++;
  pletMap[pn] = d_pfIdCounter;
  return d_pfIdCounter;
}

}  // namespace proof
}  // namespace cvc5::internal
