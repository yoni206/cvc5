#!/bin/bash
script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
release_path=$script_dir/cvc4_release
latest_path=$script_dir/cvc4_later
smt2_path=$1

release_result=`$release_path $smt2_path 2> /dev/null`
latest_result=`$latest_path $smt2_path 2> /dev/null`

if [ a$release_result = "asat" ] && [ a$latest_result = "aunsat" ]
then
	echo "reproduces"
	exit 0
else
	echo "no reproduce"
	exit 1
fi
