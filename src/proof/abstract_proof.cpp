/*
 * AbstractProof.cpp
 *
 *  Created on: Feb 21, 2018
 *      Author: yoniz
 */

#include "abstract_proof.h"


void AbstractProof::appendPremise(const std::shared_ptr<AbstractProof> premise) {
  d_premises.push_back(premise);
}

void AbstractProof::appendNodeToPremises(const Node node) {
  std::shared_ptr<AbstractProof> abstractProof =  std::make_shared<AbstractProof>(AbstractProof(node, 0));
  appendPremise(abstractProof);
}

AbstractProof::~AbstractProof() {
  // TODO Auto-generated destructor stub
}

