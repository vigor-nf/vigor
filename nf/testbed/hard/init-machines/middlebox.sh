#!/bin/bash

echo "[init] Initializing middlebox..."

pushd "$CASE_ROOT"
  ./vnds/install.sh dpdk-only # this will apt-get update
popd

sudo apt-get install -yqq \
    tcpdump git libpcap-dev \
    linux-headers-3.13.0-93 \
    libglib2.0-dev daemon iperf3 netperf tmux
