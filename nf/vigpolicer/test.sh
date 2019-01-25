#!/bin/bash

set -euo pipefail

SCRIPT_DIR=$(cd $(dirname ${BASH_SOURCE[0]}) && pwd)

function test_policer {
  INPUT_PCAP=${1}

  sudo taskset -c 8 \
      ./build/app/policer \
        --vdev "net_pcap0,rx_pcap=$INPUT_PCAP,tx_pcap=/dev/null" \
        --vdev 'net_pcap1,rx_pcap=$SCRIPT_DIR/../pcap/empty.pcap,tx_pcap=output.pcap' \
        --no-shconf -- \
        --flow-expiration 10 \
        --flow-capacity 65536 \
        --backend-capacity 20 \
        --cht-height 29 \
        --backend-expiration 60 \

#         >/dev/null 2>/dev/null
}

make clean
make ADDITIONAL_FLAGS=-DSTOP_ON_RX_0

test_policer $SCRIPT_DIR/../pcap/unirand10000.pcap
