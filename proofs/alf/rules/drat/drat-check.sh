#!/bin/bash
#echo "true"
#/space/ajreynol/cvc5-ajr/proofs/alf/rules/drat/drat-trim $1 $2
INPUT=$1
PROOF=$2

#sed -e 's/^"//' -e 's/"$//' <<<"$INPUT"
#sed -e 's/^"//' -e 's/"$//' <<<"$PROOF"
#echo "RUN: drat-trim $INPUT $PROOF"

RESULT=$(drat-trim $INPUT $PROOF)

if [[ $RESULT == *"VERIFIED"* ]];
then
      echo "true"
      exit 0
else
      echo "error: $RESULT"
      exit 1
fi
