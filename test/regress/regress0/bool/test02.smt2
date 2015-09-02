(set-logic QF_UF)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)

(declare-fun f (Bool) Bool)

(declare-fun x () Bool)
(declare-fun y () Bool)
(declare-fun z () Bool)

(assert (not (= (f (f x)) (f (f y))))) ;; => f(x) != f(y) => x != y
(assert (not (= (f y) (f z))))         ;; => y != z
(assert (not (= x z)))

(check-sat)

(exit)
