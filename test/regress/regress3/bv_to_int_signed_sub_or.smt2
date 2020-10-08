; COMMAND-LINE: --solve-bv-as-int=iand --no-check-unsat-cores
; EXPECT: unsat
(set-logic QF_BV)
(declare-fun s () (_ BitVec 4))
(declare-fun t () (_ BitVec 4))
(assert (bvsgt s t))
(assert (bvsge t (bvsub t (bvor (bvor s t) (bvneg s)))))
(check-sat)
(exit)
