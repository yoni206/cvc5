#!/usr/bin/env bash
# Reproducible compile-time benchmark for cvc5.
# Deletes only cvc5's own compiled objects (keeps external deps), then times `make -jN`.
set -e
BUILD=/home/fast/zoharyo1/git/cvc5_1/build
J=${1:-8}
TGT=${2:-}   # optional specific target, e.g. "cvc5-obj"
# Remove cvc5 TU outputs but NOT build/deps (external libs GMP/CaDiCaL/poly/symfpu...)
find "$BUILD/src" "$BUILD/test" \
    \( -name '*.o' -o -name '*.gch' -o -name '*.pch' \) -delete 2>/dev/null || true
cd "$BUILD"
START=$(date +%s.%N)
make -j"$J" $TGT > /tmp/build_log.txt 2>&1
RC=$?
END=$(date +%s.%N)
echo "exit=$RC  time=$(echo "$END - $START" | bc)s  (j=$J ${TGT:-all})"
tail -3 /tmp/build_log.txt
