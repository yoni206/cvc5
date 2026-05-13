; EXPECT: unsat
; exercises ProofRule::ARITH_POW2_DIV0_REFINE
(set-logic QF_NIA)
(declare-fun x () Int)
(assert (and (<= 0 x) (< x 16)))
(assert (< (int.pow2 x) x))
(check-sat)
