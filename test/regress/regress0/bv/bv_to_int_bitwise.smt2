; COMMAND-LINE:  --bvand-integer-granularity=1 --solve-bv-as-int=sum  --no-check-models  --no-check-unsat-cores --no-check-proofs
; COMMAND-LINE:  --bvand-integer-granularity=1 --solve-bv-as-int=iand --no-check-models  --no-check-unsat-cores --no-check-proofs
; COMMAND-LINE:  --bvand-integer-granularity=1 --solve-bv-as-int=iand --iand-mode=sum --no-check-models  --no-check-unsat-cores --no-check-proofs
; COMMAND-LINE:  --bvand-integer-granularity=1 --solve-bv-as-int=iand --iand-mode=bitwise --no-check-models  --no-check-unsat-cores --no-check-proofs
; COMMAND-LINE:  --bvand-integer-granularity=5 --solve-bv-as-int=sum  --no-check-models  --no-check-unsat-cores --no-check-proofs
; EXPECT: unsat
(set-logic QF_BV)
(declare-fun s () (_ BitVec 4))
(declare-fun t () (_ BitVec 4))
(assert (not (= (bvlshr s (bvor (bvand t #b0000) s)) #b0000)))
(check-sat)
(exit)
