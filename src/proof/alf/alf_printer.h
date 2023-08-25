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
#include <cstddef>
#include <memory>

#include "cvc5_private.h"

#ifndef CVC4__PROOF__ALF_PROOF_PRINTER_H
#define CVC4__PROOF__ALF_PROOF_PRINTER_H

#include <iostream>

#include "expr/node_algorithm.h"
#include "proof/alf/alf_print_channel.h"
#include "proof/proof_checker.h"
#include "proof/proof_node.h"

namespace cvc5::internal {

namespace proof {

class AlfPrinter
{
 public:
  AlfPrinter();
  ~AlfPrinter() {}

  /**
   * Print the full proof of assertions => false by pfn.
   */
    void print(std::ostream& out, std::shared_ptr<ProofNode> pfn);

 private:

  /**
   * For each proof node, the final AletheLF output's formatting depends on
   *  the particular proof rule. For example, a chain resolution must be
   *  converted into a series of sequential resolutions.
   * This method cases on the AletheLF proof rules (./lean_rules.h) and prints
   *  to the ostream& out.
   * Prints proof node children before parents, unless we encounter the
   *  SCOPE rule, in which case we print "assume" and bind a new variable.
   */
 void printProof(std::ostream& out,
                         std::shared_ptr<ProofNode> pfn,
                         size_t& lastStep,
                         std::map<std::shared_ptr<ProofNode>, size_t>& stepMap);

  /* Returns the proof name normalized */
  static std::string getRuleName(const ProofNode* pfn);

  void printOrdinaryStep(
      std::ostream& out,
      std::shared_ptr<ProofNode> pfn,
      const size_t& lastStep,
      std::map<std::shared_ptr<ProofNode>, size_t>& stepMap);

  //-------------
  void printProofInternal(AlfPrintChannel* out,
                          const ProofNode* pn,
                          const LetBinding& lbind,
                          std::map<const ProofNode*, size_t>& pletMap,
                          std::map<Node, size_t>& passumeMap);
  void printStepPre(AlfPrintChannel* out,
                          const ProofNode* pn,
                          const LetBinding& lbind,
                          std::map<const ProofNode*, size_t>& pletMap,
                          std::map<Node, size_t>& passumeMap);
  void printStepPost(AlfPrintChannel* out,
                          const ProofNode* pn,
                          const LetBinding& lbind,
                          std::map<const ProofNode*, size_t>& pletMap,
                          std::map<Node, size_t>& passumeMap);
  /** Allocate assume id, return true if was newly allocated */
  size_t allocateAssumeId(const Node& n, std::map<Node, size_t>& passumeMap, bool& wasAlloc);
  size_t allocateProofId(const ProofNode* pn, std::map<const ProofNode*, size_t>& pletMap, bool& wasAlloc);
  /** Assume id counter */
  size_t d_pfIdCounter;
  /** Active scopes */
  std::unordered_set<const ProofNode*> d_activeScopes;
};

}  // namespace proof
}  // namespace cvc5::internal

#endif
