; EXPECT: sat
(set-logic ALL)
(set-option :incremental false)
(set-option :finite-model-find true)
(set-option :fmf-bound-int true)
(set-option :produce-models true)
(declare-fun X () (Set Int))
(declare-fun Y () (Set Int))
(assert (forall ((x Int)) (=> (member x X) (> x 0))))
(check-sat-assuming ( (=> (and (= (card X) 5) (= Y (union X (singleton 9)))) (<= (card Y) 4)) ))