/*
 * proof_printer.h
 *
 *  Created on: Feb 22, 2018
 *      Author: yoniz
 */

#ifndef CVC4__PROOF__PRINTER_H_
#define CVC4__PROOF__PRINTER_H_

#include "abstract_proof.h"
#include "../expr/node.h"
#include "../context/cdhashmap.h"

namespace CVC4 {
namespace PROOF_PRINTER {
/**
 * print the beginning of the proof, and call orintProofRec, which prints the actual proof.
 */
static void printProof(std::ostream& out, const AbstractProof& ap);

/**
 * recursively print the actual proof.
 * for each Node n, context[n] is a name for the proof of n.
 */
static void printProofRec(std::ostream& out, const AbstractProof& ap,  context::CDHashMap<Node, unsigned>& context);

}
}
#endif /* PROOF_PRINTER_H_ */
