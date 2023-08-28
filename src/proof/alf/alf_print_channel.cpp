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

AlfPrintChannelOut::AlfPrintChannelOut(std::ostream& out,
                                       const LetBinding& lbind,
                                       const std::string& tprefix)
    : d_out(out), d_lbind(lbind), d_termLetPrefix(tprefix)
{
}

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
                                   const std::vector<Node>& premises,
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
    for (const Node& p : premises)
    {
      if (firstTime)
      {
        firstTime = false;
      }
      else
      {
        d_out << " ";
      }
      printNodeInternal(d_out, p);
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

void AlfPrintChannelOut::printTrust(PfRule r, TNode n, size_t i, TNode nc)
{
  Assert(!nc.isNull());
  if (d_warnedRules.find(r) == d_warnedRules.end())
  {
    d_out << "; WARNING: add trust step for " << r << std::endl;
    d_warnedRules.insert(r);
  }
  d_out << "; trust " << r << std::endl;
  printStep("trust", n, i, {}, {nc}, false);
}

void AlfPrintChannelOut::printNodeInternal(std::ostream& out, Node n)
{
  // due to use of special names in the node converter, we must clean symbols
  std::stringstream ss;
  options::ioutils::applyOutputLanguage(ss, Language::LANG_SMTLIB_V2_6);
  Node nc = d_lbind.convert(n, d_termLetPrefix, true);
  nc.toStream(ss);
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

AlfPrintChannelPre::AlfPrintChannelPre(LetBinding& lbind) : d_lbind(lbind) {}

void AlfPrintChannelPre::printNode(TNode n) { d_lbind.process(n); }

void AlfPrintChannelPre::printAssume(TNode n, size_t i, bool isPush)
{
  d_lbind.process(n);
}

void AlfPrintChannelPre::printStep(const std::string& rname,
                                   TNode n,
                                   size_t i,
                                   const std::vector<Node>& premises,
                                   const std::vector<Node>& args,
                                   bool isPop)
{
  if (!n.isNull())
  {
    d_lbind.process(n);
  }
  // don't process premises, even if they may be non-variable, as this
  // will introduce internal (proof) symbols into the letification
  for (const Node& a : args)
  {
    d_lbind.process(a);
  }
}
void AlfPrintChannelPre::printTrust(PfRule r, TNode n, size_t i, TNode nc)
{
  Assert(!nc.isNull());
  d_lbind.process(nc);
}

}  // namespace proof
}  // namespace cvc5::internal
