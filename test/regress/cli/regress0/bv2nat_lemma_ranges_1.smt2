; COMMAND: --model-based-arith-bv-conv
; EXPECT: unsat
(set-logic ALL)
(declare-fun x () (_ BitVec 4000))
(assert (< (bv2nat x) 0))
(check-sat)
