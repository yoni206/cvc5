; COMMAND-LINE: --decision=internal
; EXPECT: sat
(set-logic QF_SLIA)
(declare-fun s () String)
(declare-fun s1 () String)
(declare-fun s2 () String)

(assert (= "0" (str.substr s 2 1)))
(assert (distinct 1 (str.len (str.substr s 2 2))))
(assert (= 1 (str.len (str.substr s 1 1))))
(assert (= 1 (str.len (str.substr s 0 1))))
(assert (= "0" (str.at (str.substr s 3 (- (str.len s) 3)) 0)))
(assert (distinct 1 (str.len (str.substr "00000" 3 (- (str.len s) 3)))))
(assert (> (str.len s) 3))
(assert (<= (str.len s) 5))

; (assert (str.in_re s (re.+ (re.range "0" "9"))))
(assert (= s (str.++ s1 s2)))
(assert (str.in_re s1 (re.range "0" "9")))
(assert (str.in_re s2 (re.* (re.range "0" "9"))))


(check-sat)
