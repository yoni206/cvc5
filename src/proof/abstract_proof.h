/*
 * AbstractProof.h
 *
 *  Created on: Feb 21, 2018
 *      Author: yoniz
 */

#ifndef __CVC4__ABSTRACT_PROOF_H
#define __CVC4__ABSTRACT_PROOF_H

#include "../expr/node.h"
#include <vector>

using CVC4::Node;


class AbstractProof {
public:

  /**
   * This constructor can be called either with all four parameters, without parameters, or without neither of premises and parameters.
   */
  AbstractProof(Node conclusion,
                unsigned label,
                std::vector<std::shared_ptr<AbstractProof>> premises = std::vector<std::shared_ptr<AbstractProof>>(),
                std::vector<Node> parameters = std::vector<Node>() ) :
                  d_conclusion(conclusion),
                  d_label(label),
                  d_premises(premises),
                  d_parameters(parameters)
                  {}

  ~AbstractProof();

  /*
   * Add a subproof to the list of premises
   */
  void appendPremise(const std::shared_ptr<AbstractProof> premise);

  /*
   * Wrap a node as an AbstractProof and append the result to the premises
   */
  void appendNodeToPremises(const Node node);



  Node d_conclusion;

  /**
   * TODO 0 should represent either an assertion or a termporary place-holder.
   */
  unsigned d_label;
  std::vector<std::shared_ptr<AbstractProof>> d_premises;
  std::vector<Node> d_parameters;

};

#endif /* __CVC4__ABSTRACTPROOF_H */
