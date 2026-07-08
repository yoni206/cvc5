#!/usr/bin/env bash
# Paired unity-ON vs unity-OFF compile-time measurement for an already-configured
# build dir (deps already built). Rebuilds ONLY cvc5's own objects each time.
# Usage: ./measure-dir.sh <build-dir> [J]
set -u
ROOT=/home/fast/zoharyo1/git/cvc5_1
dir="$ROOT/$1"; J=${2:-8}

wipe() { find "$dir/src" "$dir/test" \( -name '*.o' -o -name '*.gch' -o -name '*.pch' \) -delete 2>/dev/null || true; }
build() { cd "$dir"; local S E; S=$(date +%s.%N); make -j"$J" >/tmp/m.log 2>&1; local rc=$?; E=$(date +%s.%N); echo "rc=$rc time=$(echo "$E - $S"|bc)s"; [ $rc -ne 0 ] && tail -15 /tmp/m.log; }

echo "### $1  (j=$J)"
echo -n "unity ON  : "; cmake "$dir" -DENABLE_UNITY_BUILD=ON  -DENABLE_PCH=OFF >/dev/null 2>&1; wipe; build
echo -n "unity OFF : "; cmake "$dir" -DENABLE_UNITY_BUILD=OFF -DENABLE_PCH=OFF >/dev/null 2>&1; wipe; build
echo -n "PCH only  : "; cmake "$dir" -DENABLE_UNITY_BUILD=OFF -DENABLE_PCH=ON  >/dev/null 2>&1; wipe; build
# restore default (unity ON)
cmake "$dir" -DENABLE_UNITY_BUILD=ON -DENABLE_PCH=ON >/dev/null 2>&1
