
; could take into account heap types

(declare-const sep.nil (-> (! Type :var T) T))
(declare-const sep.emp Bool)

(declare-const sep (-> Bool Bool Bool) :right-assoc-nil)

(declare-const wand (-> Bool Bool Bool))

(declare-const pto (-> (! Type :var U :implicit) (! Type :var T :implicit) U T Bool))

; internal
(declare-const SEP_LABEL (-> (! Type :var U :implicit) (! Type :var T :implicit) U (Set T) Bool))
