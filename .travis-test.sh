#!/bin/bash

. paths.sh

set -euxo pipefail

for nf in vig*; do
  pushd "$nf"
    make clean
    make
    make symbex validate
  popd
done

echo "All NFs succeeded"

make verifast

echo "All verifast checks pass"
