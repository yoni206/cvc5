;COMMAND: --sygus-interpol=default 
;EXPECT: unsat
(set-logic QF_UFLIA)

; Let A1,...,An be formulas (called assumptions)
; Let C be a formula (called a conjecture)
; An interpolant of {A1,...,An} and G is any formula B such that:
; - A1,...,An |- B
; - B |- C
; - B has only variables that occur both in {A_1,...,A_n} and B.


;The assumptions are:
; (*) 0 <= n
; (*) n < x
; (*) n < y
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(declare-fun n () Int)
(define-fun A1 () Bool (<= 0 n))
(define-fun A2 () Bool (< n x))
(define-fun A3 () Bool (< n y))
(assert (and A1 A2 A3))

;The conjuecture is: z < 0 --> z + 2 < x + y
;notice the conjecture does not have n in it, bot has z in it (the assumptions don't have z)
(define-fun C () Bool (=> (< z 0) (< (+ 2 z) (+ x y))))

(check-sat-assuming ((not C)))

