#!/bin/bash
CVC4_BASE_DIR=/home/yoniz/git/CVC4
CVC4_REGRESS_DIR=$CVC4_BASE_DIR/test/regress
CVC4_BIN=$CVC4_BASE_DIR/builds/debug/bin/./cvc4
for f in `grep QF_NIA -nirI $CVC4_REGRESS_DIR | cut -d: -f1`
do
  echo $f
  $CVC4_BIN $f --tlimit=5000
  $CVC4_BIN $f --solve-int-as-bv=8 --tlimit=5000
  echo
done

for f in `grep QF_UFNIA -nirI $CVC4_REGRESS_DIR | cut -d: -f1`
do
  echo $f
  $CVC4_BIN $f --tlimit=5000
  $CVC4_BIN $f --solve-int-as-bv=8 --tlimit=5000
  echo
done
