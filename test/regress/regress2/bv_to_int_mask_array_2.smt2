; COMMAND-LINE:  --solve-bv-as-int=bv --no-check-proofs
; COMMAND-LINE:  --bvand-integer-granularity=1 --solve-bv-as-int=sum    --no-check-proofs
; COMMAND-LINE:  --bvand-integer-granularity=1 --solve-bv-as-int=iand    --no-check-proofs
; COMMAND-LINE:  --bvand-integer-granularity=1 --solve-bv-as-int=iand --iand-mode=sum    --no-check-proofs
; COMMAND-LINE:  --bvand-integer-granularity=1 --solve-bv-as-int=iand --iand-mode=bitwise    --no-check-proofs
; EXPECT: sat
(set-logic ALL)
(declare-fun A () (Array Int Int))
(declare-fun f ((_ BitVec 3)) Int)
(declare-fun x () (_ BitVec 3))
(declare-fun y () (_ BitVec 3))
(assert (distinct (select A (f (bvand x y))) (select A (f (bvor x y)))))
(check-sat)
