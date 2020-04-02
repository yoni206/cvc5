; COMMAND-LINE: --solve-bv-as-int=1 --no-check-models  --no-check-unsat-cores --no-check-proofs 
; EXPECT: sat
(set-logic QF_BV)
(declare-fun _substvar_241_ () (_ BitVec 32))
(assert (let ((?x50 ((_ sign_extend 0) _substvar_241_))) (bvsle ((_ zero_extend 24) ((_ extract 7 0) (bvadd ?x50 (_ bv4294966920 32)))) (bvadd ?x50 ?x50))))
(check-sat)
(exit)
