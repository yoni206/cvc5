; COMMAND-LINE:  --solve-bv-as-int=sum --bvand-integer-granularity=1   
; COMMAND-LINE:  --solve-bv-as-int=sum --bvand-integer-granularity=4   
; COMMAND-LINE:  --solve-bv-as-int=sum --bvand-integer-granularity=8   
; EXPECT: sat
(set-logic QF_BV)
(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))
(assert (bvult (bvmul a b) (bvudiv a b)))

(check-sat)
