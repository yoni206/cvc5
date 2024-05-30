; EXPECT: unsat
(set-logic ALL)
(declare-fun x () (_ BitVec 4000))
(declare-fun y () (_ BitVec 4000))
(assert (distinct (bv2nat (bvadd x y)) (+ (bv2nat x) (bv2nat y))))
(check-sat)
