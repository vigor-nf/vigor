#!/bin/bash

echo "[init] Initializing middlebox..."

./init-machines/install-dpdk.sh

# CHANGE THIS IF YOU CHANGE THE DEPS BELOW (this allows us to not apt-get update every time)
DEPS_VERSION='1'
if [ ! -f '.deps_version' ] || [ "$(cat .deps_version)" != "$DEPS_VERSION" ]; then
  sudo apt-get -qq update
  sudo apt-get install -yqq \
    tcpdump git libpcap-dev \
    linux-headers-3.13.0-93 \
    libglib2.0-dev daemon iperf3 netperf tmux

  echo "$DEPS_VERSION" > '.deps_version'
fi
