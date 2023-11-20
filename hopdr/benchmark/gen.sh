#!/bin/sh
set -eu

cwd=`dirname $0`
cwd=`realpath $cwd`

GOLEM_BENCH="https://github.com/blishko/chc-benchmarks"
GOLEM_COMMIT="200d7efc0b8621de19127f10715cec8c41ece363"

rm -rf inputs lists
mkdir -p inputs lists

INPUTS=$cwd/inputs
LISTS=$cwd/lists

tmp_dir=$(mktemp -d -t hopdr-XXXX)
if [ $? -ne 0 ]; then
    echo "Error: Failed to create temporary file."
    exit 1
fi

cd $tmp_dir
git clone $GOLEM_BENCH && cd chc-benchmarks && git checkout $GOLEM_COMMIT
cd transition_systems/multi-phase

mkdir -p $INPUTS/golem_safe $INPUTS/golem_unsafe
cp *.smt2 $INPUTS/golem_safe
cp unsafe/*.smt2 $INPUTS/golem_unsafe
ls $INPUTS/golem_safe > $LISTS/golem_safe
ls $INPUTS/golem_unsafe > $LISTS/golem_unsafe


