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
#include "proof/alf/alf_proof_rule.h"
#include "proof/proof_node_to_sexpr.h"

namespace cvc5::internal {

namespace proof {

std::string AletheLFPrinter::getRuleName(std::shared_ptr<ProofNode> pfn)
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

void AletheLFPrinter::printOrdinaryStep(
    std::ostream& out,
    std::shared_ptr<ProofNode> pfn,
    const size_t& lastStep,
    std::map<std::shared_ptr<ProofNode>, size_t>& stepMap)
{
  out << "(step t" << lastStep << " " << pfn->getResult() << " :rule "
      << getRuleName(pfn);

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
  if ((pfn->getRule() == PfRule::ALF_RULE
       && pfn->getArguments().size() > 1)
      || (pfn->getRule() != PfRule::ALF_RULE
          && pfn->getArguments().size() > 0))
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

void AletheLFPrinter::printProof(
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

void AletheLFPrinter::printSortsAndConstants(std::ostream& out,
                                             std::shared_ptr<ProofNode> pfn)
{
  // TODO: this does something, I don't know what

  // Print user defined sorts and constants of those sorts
  std::unordered_set<Node> syms;
  std::unordered_set<TNode> visited;
  std::vector<Node> iasserts;

  const std::vector<Node>& assertions = pfn->getArguments();
  for (const Node& a : assertions)
  {
    expr::getSymbols(a, syms, visited);
    iasserts.push_back(a);
  }
  int sortCount = 1;
  int symCount = 1;
  std::unordered_set<TypeNode> sts;
  for (const Node& s : syms)
  {
    TypeNode st = s.getType();
    if (st.isUninterpretedSort() && sts.find(st) == sts.end())
    {
      // declare a user defined sort, if that sort has not been encountered
      // before
      sts.insert(st);
      out << "def " << st << " := sort.atom " << sortCount << std::endl;
      sortCount += 1;
    }
    // declare a constant of a predefined sort
    out << "def " << s << " := const " << symCount << " " << st << std::endl;
    symCount += 1;
  }
}

void AletheLFPrinter::print(std::ostream& out, std::shared_ptr<ProofNode> pfn)
{
  // outer method to print valid AletheLF output from a ProofNode
  std::map<std::shared_ptr<ProofNode>, size_t> stepMap;
  size_t lastStep = 0;

  printSortsAndConstants(out, pfn);
  printProof(out, pfn, lastStep, stepMap);
  out << "\n";
}

}  // namespace proof
}  // namespace cvc5::internal
