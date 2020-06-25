; COMMAND-LINE:  --cegqi-all --full-saturate-quant --bvand-integer-granularity=1 --solve-bv-as-int=sum     --no-check-proofs
; COMMAND-LINE:  --cegqi-all --full-saturate-quant --bvand-integer-granularity=1 --solve-bv-as-int=iand --iand-mode=sum    --no-check-proofs
; COMMAND-LINE:  --cegqi-all --full-saturate-quant --bvand-integer-granularity=1 --solve-bv-as-int=iand --iand-mode=bitwise    --no-check-proofs
; COMMAND-LINE:  --cegqi-all --full-saturate-quant --bvand-integer-granularity=1 --solve-bv-as-int=iand    --no-check-proofs
; COMMAND-LINE:  --cegqi-all --full-saturate-quant --bvand-integer-granularity=2 --solve-bv-as-int=sum     --no-check-proofs
; EXPECT: unsat
(set-logic BV)
(declare-fun s () (_ BitVec 4))
(declare-fun t () (_ BitVec 4))
(assert (bvsgt s t))
(assert (bvsge t (bvsub t (bvor (bvor s t) (bvneg s)))))
;(assert (not (bvult (bvadd t #b1000) (bvadd (bvadd t (bvadd (bvnot (bvadd (bvadd s t) (bvadd (bvnot (bvand s t)) #b0001))) #b0001)) #b1000))))
(check-sat)
(exit)
