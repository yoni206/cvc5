; COMMAND-LINE: --solve-int-as-bv=16
; EXPECT: sat
(set-logic QF_UFNIA)
(declare-const a Int)
(declare-const b Int)
(declare-fun f (Int) Int)
(assert (not (= (+ (f a) (f b)) (f (+ a b)))))
(check-sat)
