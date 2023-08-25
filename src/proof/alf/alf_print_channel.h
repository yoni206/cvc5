/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
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

#include "cvc5_private.h"

#ifndef CVC4__PROOF__LFSC__LFSC_PRINT_CHANNEL_H
#define CVC4__PROOF__LFSC__LFSC_PRINT_CHANNEL_H

#include <iostream>
#include <map>

#include "expr/node.h"
#include "printer/let_binding.h"
#include "proof/lfsc/lfsc_util.h"
#include "proof/proof_node.h"
#include "rewriter/rewrite_proof_rule.h"

namespace cvc5::internal {
namespace proof {

/**
 * LFSC proofs are printed in two phases: the first phase computes the
 * letification of terms in the proof as well as other information that is
 * required for printing the preamble of the proof. The second phase prints the
 * proof to an output stream. This is the base class for these two phases.
 */
class AlfPrintChannel
{
 public:
  AlfPrintChannel() {}
  virtual ~AlfPrintChannel() {}
  /** Print node n */
  virtual void printNode(TNode n) {}
  /** Print type node n */
  virtual void printTypeNode(TypeNode tn) {}
  /** Print assume */
  virtual void printAssume(TNode n, size_t i, bool isPush = false) {}
  /** Print step */
  virtual void printStep(const std::string& rname,
                         TNode n,
                         size_t i,
                         const std::vector<size_t>& premises,
                         const std::vector<Node>& args,
                         bool isPop)
  {
  }
};

/** Prints the proof to output stream d_out */
class AlfPrintChannelOut : public AlfPrintChannel
{
 public:
  AlfPrintChannelOut(std::ostream& out);
  void printNode(TNode n) override;
  void printTypeNode(TypeNode tn) override;
  void printAssume(TNode n, size_t i, bool isPush) override;
  void printStep(const std::string& rname,
                 TNode n,
                 size_t i,
                 const std::vector<size_t>& premises,
                 const std::vector<Node>& args,
                 bool isPop) override;

  /**
   * Print node to stream in the expected format of LFSC.
   */
  static void printNodeInternal(std::ostream& out, Node n);
  /**
   * Print type node to stream in the expected format of LFSC.
   */
  static void printTypeNodeInternal(std::ostream& out, TypeNode tn);
  static void printRule(std::ostream& out, const ProofNode* pn);

 private:
  /** The output stream */
  std::ostream& d_out;
};

/**
 * Run on the proof before it is printed, and does two preparation steps:
 * - Computes the letification of nodes that appear in the proof.
 * - Computes the set of DSL rules that appear in the proof.
 */
class AlfPrintChannelPre : public AlfPrintChannel
{
 public:
  AlfPrintChannelPre(LetBinding& lbind);
  void printNode(TNode n) override;
  void printAssume(TNode n, size_t i, bool isPush) override;
  void printStep(const std::string& rname,
                 TNode n,
                 size_t i,
                 const std::vector<size_t>& premises,
                 const std::vector<Node>& args,
                 bool isPop) override;

 private:
  /** The let binding */
  LetBinding& d_lbind;
};

}  // namespace proof
}  // namespace cvc5::internal

#endif
