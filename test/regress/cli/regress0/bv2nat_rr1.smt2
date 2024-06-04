; EXPECT: unsat
; COMMAND: --bv2nat-plus-dist-rr
(set-logic ALL)
(declare-fun x () (_ BitVec 4000))
(declare-fun y () (_ BitVec 4000))
(assert (distinct (bv2nat (bvadd x y)) (mod (+ (bv2nat x) (bv2nat y)) (^ 2 4000))))
(check-sat)
