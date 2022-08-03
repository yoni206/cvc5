(set-logic HO_ALL)
(set-info :status sat)
(set-option :fmf-bound true)
(set-option :uf-lazy-ll true)
(set-option :strings-exp true)
(define-fun min ((x String) (y String)) String (ite (str.< x y) x y))
(declare-fun A () (Set String))
(declare-fun x () String)
(declare-fun minimum () String)
(assert (= minimum (set.fold min "zzz" A)))
(assert (str.< "aaa" minimum ))
(assert (str.< minimum "zzz"))
(assert (distinct x minimum))
(assert (set.member x A))
(check-sat)