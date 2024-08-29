; COMMAND-LINE: --model-based-arith-bv-conv=lemmas
; EXPECT: unsat
(set-logic ALL)
(declare-fun x () (_ BitVec 4))
(declare-fun y () (_ BitVec 4))
(assert (< (bv2nat x) (bv2nat y) ))
(assert (= (+ (bv2nat x) (bv2nat y)) 0))
(check-sat)
