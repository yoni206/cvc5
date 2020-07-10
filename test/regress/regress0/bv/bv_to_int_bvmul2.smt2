; COMMAND-LINE:  --solve-bv-as-int=bv --no-check-proofs --no-check-unsat-cores
; COMMAND-LINE:  --solve-bv-as-int=sum --bvand-integer-granularity=1    --no-check-proofs --no-check-unsat-cores
; EXPECT: unsat
(set-logic QF_BV)
(declare-fun T4_180 () (_ BitVec 16))
(assert (and 
(= (bvmul T4_180 (_ bv1056 16)) (_ bv0 16)) 
(not (= (bvmul T4_180 (_ bv1408 16)) (_ bv0 16))) 
)
)
(check-sat)
