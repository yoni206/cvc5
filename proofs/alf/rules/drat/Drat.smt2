(include "../../theories/Builtin.smt2")
(include "../../theories/Strings.smt2")

(program to_drat_lit ((l Bool))
  (Bool) Int
  (
    ((to_drat_lit (not l))  (alf.neg (alf.hash l)))
    ((to_drat_lit l)        (alf.hash l))
  )
)
(program to_drat_clause ((l Bool) (C Bool :list))
  (Bool) String
  (
    ((to_drat_clause false)    "0")
    ((to_drat_clause (or l C)) (alf.concat (alf.to_str (to_drat_lit l)) " " (to_drat_clause C)))
    ((to_drat_clause l)        (alf.concat (alf.to_str (to_drat_lit l)) " 0"))
  )
)

(program to_drat_input ((C Bool) (F Bool :list))
  (Bool) String
  (
    ((to_drat_input true)       "")
    ((to_drat_input (and C F)) (alf.concat (to_drat_clause C) " " (to_drat_input F)))
  )
)

; ./dratt-verify.sh takes:
; - A string corresponding to a DIMACS declaration of the input with an arbitrary mapping,
; in particular, the mapping is determined by alf.hash in the side conditions above.
; - A DRAT proof file, whose file name is given as a String.
; It returns "true" if the preamble of the DRAT proof file matches (modulo renaming
; identifiers) the input clauses, as determined by the first arguments.

(declare-oracle-fun drat-verify (String String) Bool ./drat-verify.sh)

; ./drat-check.sh
; - A DRAT proof file, whose file name is given as a String.
; It returns "true" if the DRAT proof file is a valid refutation proof.

(declare-oracle-fun drat-check (String String) Bool ./drat-check.sh)

; The DRAT proof rule.
; Takes arbitrary list of premises, an atom mapping, and the file name of a DRAT
; proof and invokes the two oracles above.

(declare-rule drat_refutation ((F Bool) (D String) (P String))
  :premise-list F and
  :args (D P)
  :requires (((drat-verify (to_drat_input F) D) true) ((drat-check D P) true))
;  :requires (((drat-verify (to_drat_input F) D) true))
;  :requires (((drat-check D P) true))
  :conclusion false
)
