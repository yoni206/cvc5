; EXPECT: unsat
; exercises ProofRule::ARITH_POW2_LOWER_BOUND_REFINE
(set-logic QF_NIA)
(declare-fun x () Int)
(assert (>= x 20))
(assert (<= x 30))
(assert (< (int.pow2 x) 1000))
(check-sat)
