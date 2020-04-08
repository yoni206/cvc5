; COMMAND-LINE: --solve-bv-as-int=1 --no-check-models  --no-check-unsat-cores --no-check-proofs --nl-ext-tplanes
; COMMAND-LINE: --solve-bv-as-int=2 --no-check-models  --no-check-unsat-cores --no-check-proofs --nl-ext-tplanes
; COMMAND-LINE: --solve-bv-as-int=2 --optimize-bv-as-int --no-check-models  --no-check-unsat-cores --no-check-proofs --nl-ext-tplanes

; EXPECT: unsat
(set-logic QF_BV)
(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))
(assert (bvult (bvor a b) (bvand a b)))
(check-sat)
