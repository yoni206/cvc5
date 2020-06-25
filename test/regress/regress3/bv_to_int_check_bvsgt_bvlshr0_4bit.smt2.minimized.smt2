; COMMAND-LINE:  --cegqi-all --full-saturate-quant --bvand-integer-granularity=1 --solve-bv-as-int=sum     --no-check-proofs
; COMMAND-LINE:  --cegqi-all --full-saturate-quant --bvand-integer-granularity=1 --solve-bv-as-int=iand --iand-mode=sum    --no-check-proofs
; COMMAND-LINE:  --cegqi-all --full-saturate-quant --bvand-integer-granularity=1 --solve-bv-as-int=iand --iand-mode=bitwise    --no-check-proofs
; COMMAND-LINE:  --cegqi-all --full-saturate-quant --bvand-integer-granularity=1 --solve-bv-as-int=iand    --no-check-proofs
; COMMAND-LINE:  --cegqi-all --full-saturate-quant --bvand-integer-granularity=2 --solve-bv-as-int=sum     --no-check-proofs
; EXPECT: unsat
(set-logic ALL)
(declare-fun t () (_ BitVec 4))
(declare-fun s () (_ BitVec 4))
(assert (bvult (_ bv8 4) (bvadd (_ bv8 4) (bvlshr t s))))
(assert (forall ((x (_ BitVec 4))) (bvule (bvadd (_ bv8 4) (bvlshr x s)) (_ bv8 4))))
(check-sat)
(exit)
