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
#include "proof/proof_checker.h"
#include "proof/proof_node.h"
#include "proof/alf/alf_print_channel.h"

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
  static void print(std::ostream& out, std::shared_ptr<ProofNode> pfn);

 private:
  /**
   * Print user defined sorts and constants of those sorts
   */
  static void printSortsAndConstants(std::ostream& out,
                                     std::shared_ptr<ProofNode> pfn);

  /**
   * For each proof node, the final AletheLF output's formatting depends on
   *  the particular proof rule. For example, a chain resolution must be
   *  converted into a series of sequential resolutions.
   * This method cases on the AletheLF proof rules (./lean_rules.h) and prints
   *  to the ostream& out.
   * Prints proof node children before parents, unless we encounter the
   *  SCOPE rule, in which case we print "assume" and bind a new variable.
   */
  static void printProof(std::ostream& out,
                         std::shared_ptr<ProofNode> pfn,
                         size_t& lastStep,
                         std::map<std::shared_ptr<ProofNode>, size_t>& stepMap);

  /* Returns the proof name normalized */
  static std::string getRuleName(std::shared_ptr<ProofNode> pfn);


  static void printOrdinaryStep(
      std::ostream& out,
      std::shared_ptr<ProofNode> pfn,
      const size_t& lastStep,
      std::map<std::shared_ptr<ProofNode>, size_t>& stepMap);
  
  //-------------
void printProofInternal(
    AlfPrintChannel* out,
    const ProofNode* pn,
    const LetBinding& lbind,
    const std::map<const ProofNode*, size_t>& pletMap,
    std::map<Node, size_t>& passumeMap);
};

}  // namespace proof
}  // namespace cvc5::internal

#endif
