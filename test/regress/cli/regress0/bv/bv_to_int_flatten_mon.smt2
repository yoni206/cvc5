; COMMAND-LINE: --solve-bv-as-int=iand
; EXPECT: sat
(set-logic ALL)
(declare-const x (_ BitVec 4))
(declare-const y (_ BitVec 4))
(assert (bvult x (bvmul y (bvshl y y) (bvxor x y))))
(check-sat)
