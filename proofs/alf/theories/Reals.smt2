(include "../theories/Arith.smt2")

; real-specific operators

(declare-const / (-> (! Type :var T :implicit)
                     (! Type :var U :implicit)
                     T U
                     (! Real :requires ((is_arith_type T) true) :requires ((is_arith_type U) true))) :left-assoc)

; internal

(declare-const /_total (-> (! Type :var T :implicit)
                           (! Type :var U :implicit)
                           T U
                           (! Real :requires ((is_arith_type T) true) :requires ((is_arith_type U) true))) :left-assoc)

(declare-const INDEXED_ROOT_PREDICATE (-> Int Bool Real Bool))

; skolems
(declare-const @k.DIV_BY_ZERO (-> Real Real))