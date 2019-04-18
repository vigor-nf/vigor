#!/bin/bash

. paths.sh

set -euxo pipefail


# TODO: make verify-* (use travis jobs to parellelize)
pushd nf/vignat
  make clean
  make
  make verify-dpdk
  make verify-hardware-nf.bc
  make verify-dsos-nf.bc
popd
pushd nf/vigbridge
  make clean
  make
  make verify-dpdk
  make verify-hardware-nf.bc
  make verify-dsos-nf.bc
popd
pushd nf/vigbalancer
  make clean
  make
  make verify-dpdk
  make verify-hardware-nf.bc
  make verify-dsos-nf.bc
popd
pushd nf/vigpolicer
  make clean
  make
  make verify-dpdk
  make verify-hardware-nf.bc
  make verify-dsos-nf.bc
popd
pushd nf/vigfw
make clean
make
make verify-dpdk
popd

echo "All symbex succeeded"

pushd nf
  make verifast
popd

echo "All verifast checks pass"

pushd validator
  make all
  mkdir test-results
  make check -j$(nproc)
  rm -r test-results
popd

echo "All validator checks pass"
