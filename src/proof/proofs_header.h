/*
 * proofs_header.h
 *
 *  Created on: Feb 22, 2018
 *      Author: yoniz
 */

#ifndef __CVC4__PROOFS_HEADER_H
#define __CVC4__PROOFS_HEADER_H

enum PROOF_RULE_IDENTIFIER {
  THEORY_BASE_TRANS,
  THEORY_BASE_REF
};

class ProofRule {
public:
  PROOF_RULE_IDENTIFIER d_id;
  std::string d_sigFileName;
  std::string d_ruleName;
  unsigned d_numOfPremises;
  unsigned d_numOfSCParameters;
};

/**
 * This is a map from rule identifiers to their specifications.
 * Each rule specification consists of:
 *      number of premises to the rules
 *      number of inputs to the side condition
 *
 */

  static std::map<PROOF_RULE_IDENTIFIER, ProofRule> rules {
    {THEORY_BASE_TRANS, {THEORY_BASE_TRANS, "th_base.plf", "trans", 2, 0}}

  };


#endif /* PROOFS_HEADER_H_ */
