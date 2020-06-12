; COMMAND-LINE: --iand-mode=sum --bvand-integer-granularity=1 --cegqi-all
; COMMAND-LINE: --iand-mode=sum --bvand-integer-granularity=2 --cegqi-all
; COMMAND-LINE: --iand-mode=bitwise --cegqi-all
; COMMAND-LINE: --iand-mode=value --cegqi-all
; EXPECT: sat
(set-logic NIA)
(set-info :status sat)
(assert (forall ((x Int) (y Int)) (=> (<= 0 x y 15) (<= ((_ iand 4) x y) x))))
(check-sat)
