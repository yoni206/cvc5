#!/bin/bash

# first input -- cvc5 binary
# second input -- ethos binary

# prepend includes
echo (include "theories/Ints.eo") > reg_eval.eo
echo (include "programs/Arith.eo") > reg_eval.eo
echo (include "theories/Strings.eo") > reg_eval.eo 
echo (include "rules/Strings.eo") > reg_eval.eo
echo (include "programs/Strings.eo") > reg_eval.eo
echo (include "rules/Strings.eo") > reg_eval.eo

# produce proof (remove `unsat` line)
$1 --dump-proofs --proof-format-mode=cpc --proof-granularity=dsl-rewrite reg_eval.smt2 | tail -n +2 > reg_eval.eo 



# check the proof
$2 reg_eval.eo

# check another proof
ethos tmp.eo
