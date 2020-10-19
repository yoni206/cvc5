; EXPECT: sat
(set-logic UFBV)
(set-option :solve-bv-as-int sum)
(declare-const bv_56-0 (_ BitVec 56))
(assert (forall ((q3 (_ BitVec 56)) (q4 (_ BitVec 56))) (not (bvugt q4 (bvudiv bv_56-0 bv_56-0)))))
(check-sat)