(set-logic AFPDTLIRA)
(assert (and (exists ((i Int)) (and (exists ((i Int)) (and (exists ((i Int)) (or (forall ((o (_ BitVec 1))) (or (forall ((o (_ BitVec 1))) (or (forall ((t (_ BitVec 1))) (or (forall ((t (_ BitVec 1))) (bvule (_ bv1 1) (bvshl (_ bv1 1) ((_ int2bv 1) i))))))))))))))))))
(check-sat)
