/******************************************************************************
 * Top contributors (to current version):
 *   Hanna Lachnitt, Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of Alf proof rules
 */

#include "proof/alf/alf_proof_rule.h"

#include <iostream>

#include "proof/proof_checker.h"

namespace cvc5::internal {

namespace proof {

const char* AlfRuleToString(AlfRule id)
{
  switch (id)
  {
    case AlfRule::AND_INTRO_NARY: return "and_intro_nary";
    case AlfRule::CHAIN_RESOLUTION: return "chain_resolution";
    case AlfRule::CONG: return "cong";
    case AlfRule::HO_CONG: return "ho_cong";
    case AlfRule::SCOPE: return "scope";
    case AlfRule::PROCESS_SCOPE: return "process_scope";
    //================================================= Undefined rule
    case AlfRule::UNDEFINED: return "undefined";
    default: return "?";
  }
}

std::ostream& operator<<(std::ostream& out, AlfRule id)
{
  out << AlfRuleToString(id);
  return out;
}

AlfRule getAlfRule(Node n)
{
  uint32_t id;
  if (ProofRuleChecker::getUInt32(n, id))
  {
    return static_cast<AlfRule>(id);
  }
  return AlfRule::UNDEFINED;
}

}  // namespace proof

}  // namespace cvc5::internal