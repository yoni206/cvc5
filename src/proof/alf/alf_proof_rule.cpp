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
 * Implementation of AletheLF proof rules
 */

#include "proof/alf/alf_proof_rule.h"

#include <iostream>

#include "proof/proof_checker.h"

namespace cvc5::internal {

namespace proof {

const char* aletheLFRuleToString(AletheLFRule id)
{
  switch (id)
  {
    case AletheLFRule::AND_INTRO_NARY: return "and_intro_nary";
    case AletheLFRule::CHAIN_RESOLUTION: return "chain_resolution";
    case AletheLFRule::CONG: return "cong";
    case AletheLFRule::HO_CONG: return "ho_cong";
    //================================================= Undefined rule
    case AletheLFRule::UNDEFINED: return "undefined";
    default: return "?";
  }
}

std::ostream& operator<<(std::ostream& out, AletheLFRule id)
{
  out << aletheLFRuleToString(id);
  return out;
}

AletheLFRule getAletheLFRule(Node n)
{
  uint32_t id;
  if (ProofRuleChecker::getUInt32(n, id))
  {
    return static_cast<AletheLFRule>(id);
  }
  return AletheLFRule::UNDEFINED;
}

}  // namespace proof

}  // namespace cvc5::internal
