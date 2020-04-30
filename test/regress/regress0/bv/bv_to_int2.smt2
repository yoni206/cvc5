; COMMAND-LINE: --solve-bv-as-int --solve-bv-as-int-granularity=1 --no-check-models  --no-check-unsat-cores
; COMMAND-LINE: --solve-bv-as-int --solve-bv-as-int-granularity=5 --no-check-models  --no-check-unsat-cores
; COMMAND-LINE: --solve-bv-as-int --solve-bv-as-int-granularity=8 --no-check-models  --no-check-unsat-cores
; EXPECT: sat
(set-logic QF_BV)
(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))
(assert (bvult (bvshl a b) (bvlshr a b)))

(check-sat)
