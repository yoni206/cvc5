#!/usr/bin/env bash
# Multi-configuration compile test for the unity/PCH speedup.
# For each config: configure (own build dir, --auto-download), build with unity
# ON (timed), smoke-test the produced binary. Logs everything.
#
# Usage: ./build-configs.sh <name> "<configure.sh args>"
#   e.g. ./build-configs.sh prod "production"
# Always appends --auto-download.
set -u
ROOT=/home/fast/zoharyo1/git/cvc5_1
J=${J:-8}
name=$1; shift
cfgargs="$*"
dir="build-$name"
log=/tmp/cfg-$name.log
: > "$log"

echo "==== [$name] configure: $cfgargs --auto-download ====" | tee -a "$log"
cd "$ROOT"
./configure.sh $cfgargs --auto-download --name="$dir" >>"$log" 2>&1
rc=$?
if [ $rc -ne 0 ]; then echo "[$name] CONFIGURE FAILED rc=$rc" | tee -a "$log"; exit 20; fi

echo "==== [$name] build (unity ON) make -j$J ====" | tee -a "$log"
cd "$ROOT/$dir"
S=$(date +%s.%N)
make -j"$J" >>"$log" 2>&1
rc=$?
E=$(date +%s.%N)
T=$(echo "$E - $S" | bc)
if [ $rc -ne 0 ]; then
  echo "[$name] BUILD FAILED rc=$rc  (see $log)" | tee -a "$log"
  echo "---- last 25 lines ----"; tail -25 "$log"
  exit 21
fi
echo "[$name] BUILD OK  unity-on time=${T}s" | tee -a "$log"

# locate the cvc5 binary
bin=$(find "$ROOT/$dir/bin" -maxdepth 1 -name 'cvc5*' -type f 2>/dev/null | head -1)
echo "[$name] binary: $bin" | tee -a "$log"
if [ -n "$bin" ]; then
  printf '(set-logic QF_LIA)(declare-fun x () Int)(assert (> x 5))(check-sat)\n' > /tmp/s-$name.smt2
  printf '(set-logic QF_LIA)(declare-fun x () Int)(assert (and (> x 5)(< x 4)))(check-sat)\n' > /tmp/u-$name.smt2
  r1=$("$bin" /tmp/s-$name.smt2 2>&1)
  r2=$("$bin" /tmp/u-$name.smt2 2>&1)
  echo "[$name] smoke: sat-case=$r1  unsat-case=$r2" | tee -a "$log"
fi
echo "[$name] DONE unity-on=${T}s rc-build=0" | tee -a "$log"
