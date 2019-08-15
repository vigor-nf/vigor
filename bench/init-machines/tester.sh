#!/bin/bash

echo "[init] Initializing tester..."


# CHANGE THIS IF YOU CHANGE THE DEPS BELOW (this allows us to not apt-get update every time)
DEPS_VERSION='1'
if [ ! -f '.deps_version' ] || [ "$(cat .deps_version)" != "$DEPS_VERSION" ]; then
  sudo apt-get -qq update

  sudo apt-get install -yqq \
    tcpdump hping3 python-scapy git \
    libpcap-dev libglib2.0-dev \
    daemon iperf3 netperf liblua5.2-dev \
    make binutils gcc \
    bc cmake

  echo "$DEPS_VERSION" > '.deps_version'
fi

~/scripts/init-machines/install-dpdk.sh
~/scripts/init-machines/install-moongen.sh
