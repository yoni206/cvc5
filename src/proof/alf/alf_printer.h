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
#include "proof/alf/alf_node_converter.h"
#include "proof/proof_checker.h"
#include "proof/proof_node.h"
#include "smt/env_obj.h"

namespace cvc5::internal {

namespace proof {

class AlfPrinter : protected EnvObj
{
 public:
  AlfPrinter(Env& env, AlfNodeConverter& atp);
  ~AlfPrinter() {}

  /**
   * Print the full proof of assertions => false by pfn.
   */
  void print(std::ostream& out, std::shared_ptr<ProofNode> pfn);

 private:
  /** Is handled? */
  bool isHandled(const ProofNode* pfn) const;
  /* Returns the proof name normalized */
  static std::string getRuleName(const ProofNode* pfn);

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
  size_t allocateAssumeId(const Node& n,
                          std::map<Node, size_t>& passumeMap,
                          bool& wasAlloc);
  size_t allocateProofId(const ProofNode* pn,
                         std::map<const ProofNode*, size_t>& pletMap,
                         bool& wasAlloc);
  /** The term processor */
  AlfNodeConverter& d_tproc;
  /** Assume id counter */
  size_t d_pfIdCounter;
  /** Active scopes */
  std::unordered_set<const ProofNode*> d_activeScopes;
};

}  // namespace proof
}  // namespace cvc5::internal

#endif
