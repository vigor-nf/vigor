#!/bin/bash

. paths.sh

set -euxo pipefail

# TODO: make verify-* (use travis jobs to parellelize)
for nf in vig*; do
  pushd "$nf"
    make clean
    make
    make verify-dpdk
    make verify-hardware-nf.bc
    make verify-dsos-nf.bc
  popd
done

echo "All symbex succeeded"

make verifast

echo "All verifast checks pass"

pushd validator
  make all
  mkdir test-results
  make check -j$(nproc)
  rm -r test-results
popd

echo "All validator checks pass"
