; EXPECT: unsat
; DISABLE-TESTER: alethe
; exercises ProofRule::ARITH_POW2_MONOTONE_REFINE
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (<= 0 x))
(assert (< x y))
(assert (>= (int.pow2 x) (int.pow2 y)))
(check-sat)
