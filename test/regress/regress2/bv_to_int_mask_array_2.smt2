; COMMAND-LINE: --solve-bv-as-int=1 --no-check-models  --no-check-unsat-cores --no-check-proofs
; COMMAND-LINE: --solve-bv-as-int=1 --bv-to-int-iand --no-check-models  --no-check-unsat-cores --no-check-proofs
; COMMAND-LINE: --solve-bv-as-int=1 --bv-to-int-iand --bv-to-int-iand=sum --no-check-models  --no-check-unsat-cores --no-check-proofs
; COMMAND-LINE: --solve-bv-as-int=1 --bv-to-int-iand --bv-to-int-iand=bitwise --no-check-models  --no-check-unsat-cores --no-check-proofs
; EXPECT: sat
(set-logic ALL)
(declare-fun A () (Array Int Int))
(declare-fun f ((_ BitVec 3)) Int)
(declare-fun x () (_ BitVec 3))
(declare-fun y () (_ BitVec 3))
(assert (distinct (select A (f (bvand x y))) (select A (f (bvor x y)))))
(check-sat)
