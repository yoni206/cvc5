; EXPECT: unsat
; DISABLE-TESTER: alethe
; exercises ProofRule::ARITH_POW2_VALUE_REFINE
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (<= 7 x))
(assert (>= 9 x))
(assert (> (* 2 (* x x)) (int.pow2 x)))
(check-sat)
