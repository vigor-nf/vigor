#!/bin/bash

. ../paths.sh

set -euxo pipefail

for nf in vig*; do
  pushd "$nf"
    make
    make symbex #validate is too slow for Travis :(
  popd
done

echo "All NFs succeeded"

make verifast

echo "All verifast checks pass"
