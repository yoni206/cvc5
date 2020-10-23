; EXPECT: sat
(set-logic UFBV)
(set-option :solve-bv-as-int sum)
(declare-const bv_56-0 (_ BitVec 4))
(assert (forall ((q4 (_ BitVec 4))) (not (bvugt q4 (bvudiv bv_56-0 bv_56-0)))))
(check-sat)