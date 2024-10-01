(set-logic ALL)
(assert (str.in_re "a" (str.to_re "b")))
(check-sat)
