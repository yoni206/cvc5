/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for issue #6111
 *
 */

#include <cvc5/cvc5.h>

int main() {
  cvc5::Solver solver;

  // allow recursive datatype
  // solver.setOption("dt-cyclic", "true");
  // solver.setOption("dt-nested-rec", "true");
  solver.setOption("trace", "datatypes-prereg");


  // the recursive datatype declaration:
  // datatype A {
  //   v1,
  //   v2,
  //   v3 { value: array[A -> A] },
  // }
  auto sort_placeholder = solver.mkUnresolvedDatatypeSort("A", 0);
  auto decl = solver.mkDatatypeDecl("A");
  auto v1 = solver.mkDatatypeConstructorDecl("v1");
  decl.addConstructor(v1);
  auto v2 = solver.mkDatatypeConstructorDecl("v2");
  decl.addConstructor(v2);
#ifndef IGNORE_NESTED
  auto v3 = solver.mkDatatypeConstructorDecl("v3");
  v3.addSelector("value",
                 solver.mkArraySort(sort_placeholder, sort_placeholder));
  decl.addConstructor(v3);
#endif
  auto sort_a = solver.mkDatatypeSort(decl);

  // create two dummy terms, both of sort A, with v1 and v2 variants
  auto v1_ctor = sort_a.getDatatype().getConstructor("v1").getTerm();
  auto term_v1 = solver.mkTerm(cvc5::APPLY_CONSTRUCTOR, {v1_ctor});
  auto v2_ctor = sort_a.getDatatype().getConstructor("v2").getTerm();
  auto term_v2 = solver.mkTerm(cvc5::APPLY_CONSTRUCTOR, {v2_ctor});

  // create the array term: (constant array)
  auto sort_array_of_a_to_a = solver.mkArraySort(sort_a, sort_a);
  auto term_array = solver.mkConstArray(sort_array_of_a_to_a, term_v1);

  // update the array with a store
  auto term_a_array_updated =
      solver.mkTerm(cvc5::STORE, {term_array, term_v2, term_v2});
  auto assertion = solver.mkTerm(cvc5::EQUAL, {term_a_array_updated, term_array});
  solver.assertFormula(assertion);
  solver.checkSat();
  // SIMPLIFICATION TRIGGERS A PANIC HERE!
  solver.simplify(term_a_array_updated);
}
