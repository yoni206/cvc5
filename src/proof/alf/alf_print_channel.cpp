/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Print channels for LFSC proofs.
 */

#include "proof/alf/alf_print_channel.h"

#include <sstream>

#include "proof/alf/alf_proof_rule.h"

using namespace cvc5::internal::rewriter;

namespace cvc5::internal {
namespace proof {

AlfPrintChannelOut::AlfPrintChannelOut(std::ostream& out) : d_out(out) {}

void AlfPrintChannelOut::printNode(TNode n)
{
  d_out << " ";
  printNodeInternal(d_out, n);
}

void AlfPrintChannelOut::printTypeNode(TypeNode tn)
{
  d_out << " ";
  printTypeNodeInternal(d_out, tn);
}

void AlfPrintChannelOut::printAssume(TNode n, size_t i, bool isPush)
{
  Assert(!n.isNull());
  d_out << "(" << (isPush ? "push" : "assume") << " @p" << i;
  printNode(n);
  d_out << ")" << std::endl;
}
void AlfPrintChannelOut::printStep(const std::string& rname,
                                   TNode n,
                                   size_t i,
                                   const std::vector<size_t>& premises,
                                   const std::vector<Node>& args,
                                   bool isPop)
{
  d_out << "(" << (isPop ? "pop" : "step") << " @p" << i;
  if (!n.isNull())
  {
    printNode(n);
  }
  d_out << " :rule " << rname;
  bool firstTime = true;
  if (!premises.empty())
  {
    d_out << " :premises (";
    for (size_t p : premises)
    {
      if (firstTime)
      {
        firstTime = false;
      }
      else
      {
        d_out << " ";
      }
      d_out << "@p" << p;
    }
    d_out << ")";
  }
  if (!args.empty())
  {
    d_out << " :args (";
    firstTime = true;
    for (const Node& a : args)
    {
      if (firstTime)
      {
        firstTime = false;
      }
      else
      {
        d_out << " ";
      }
      printNodeInternal(d_out, a);
    }
    d_out << ")";
  }
  d_out << ")" << std::endl;
}

void AlfPrintChannelOut::printTrust(PfRule r, TNode n, size_t i)
{
  d_out << "; trust " << r << std::endl;
  printStep("trust", n, i, {}, {n}, false);
}

void AlfPrintChannelOut::printNodeInternal(std::ostream& out, Node n)
{
  // due to use of special names in the node converter, we must clean symbols
  std::stringstream ss;
  options::ioutils::applyOutputLanguage(ss, Language::LANG_SMTLIB_V2_6);
  n.toStream(ss);
  std::string s = ss.str();
  // cleanSymbols(s);
  out << s;
}

void AlfPrintChannelOut::printTypeNodeInternal(std::ostream& out, TypeNode tn)
{
  // due to use of special names in the node converter, we must clean symbols
  std::stringstream ss;
  options::ioutils::applyOutputLanguage(ss, Language::LANG_SMTLIB_V2_6);
  tn.toStream(ss);
  std::string s = ss.str();
  // cleanSymbols(s);
  out << s;
}

void AlfPrintChannelOut::printRule(std::ostream& out, const ProofNode* pn)
{
  if (pn->getRule() == PfRule::ALF_RULE)
  {
    const std::vector<Node>& args = pn->getArguments();
    out << getAlfRule(args[0]);
    return;
  }
  // Otherwise, convert to lower case
  std::stringstream ss;
  ss << pn->getRule();
  std::string rname = ss.str();
  std::transform(
      rname.begin(), rname.end(), rname.begin(), [](unsigned char c) {
        return std::tolower(c);
      });
  out << rname;
}

AlfPrintChannelPre::AlfPrintChannelPre(LetBinding& lbind) : d_lbind(lbind) {}

void AlfPrintChannelPre::printNode(TNode n) { d_lbind.process(n); }

void AlfPrintChannelPre::printAssume(TNode n, size_t i, bool isPush)
{
  d_lbind.process(n);
}

void AlfPrintChannelPre::printStep(const std::string& rname,
                                   TNode n,
                                   size_t i,
                                   const std::vector<size_t>& premises,
                                   const std::vector<Node>& args,
                                   bool isPop)
{
  if (!n.isNull())
  {
    d_lbind.process(n);
  }
  for (const Node& a : args)
  {
    d_lbind.process(a);
  }
}

}  // namespace proof
}  // namespace cvc5::internal
