; EXPECT: unsat
; DISABLE-TESTER: alethe
; exercises ProofRule::ARITH_POW2_INIT_REFINE
(set-logic QF_NIA)
(declare-fun x () Int)
(assert (> x 0))
(assert (< 0 (mod (int.pow2 x) 2)))
(check-sat)
