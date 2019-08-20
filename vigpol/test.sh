#!/bin/bash

set -euo pipefail

SCRIPT_DIR=$(cd $(dirname ${BASH_SOURCE[0]}) && pwd)

function cleanup {
  sudo killall policer 2>/dev/null || true
  sudo killall iperf 2>/dev/null || true
  sudo ip netns delete lan 2>/dev/null || true
  sudo ip netns delete wan 2>/dev/null || true
}
trap cleanup EXIT


function test_policer {
  RATE=$1
  BURST=$2

  sudo taskset -c 8 \
      ./build/app/policer \
        --vdev "net_tap0,iface=test_wan" \
        --vdev "net_tap1,iface=test_lan" \
        --no-shconf -- \
        --lan 3 \
        --wan 2 \
        --rate $RATE \
        --burst $BURST \
        --capacity 65536 \
        >/dev/null 2>/dev/null &
  NF_PID=$!

  while [ ! -f /sys/class/net/test_lan/tun_flags -o
          ! -f /sys/class/net/test_lan/tun_flags ]; do
    echo "Waiting for NF to launch...";
    sleep 1;
  done
  sleep 2

  sudo ip netns add lan
  sudo ip link set test_lan netns lan
  sudo ip netns exec lan ifconfig test_lan up 10.0.0.1
  LAN_MAC=$(sudo ip netns exec lan ifconfig test_lan | head -n 1 | awk '{ print $5 }')

  sudo ip netns add wan
  sudo ip link set test_wan netns wan
  sudo ip netns exec wan ifconfig test_wan up 10.0.0.2
  WAN_MAC=$(sudo ip netns exec wan ifconfig test_wan | head -n 1 | awk '{ print $5 }')

  sudo ip netns exec lan arp -i test_lan -s 10.0.0.2 $WAN_MAC
  sudo ip netns exec wan arp -i test_wan -s 10.0.0.1 $LAN_MAC

  sudo ip netns exec lan iperf -us -i 1 &
  SERVER_PID=$!

  sudo ip netns exec wan iperf -uc 10.0.0.1 -t 10 >/dev/null

  sudo killall iperf
  wait $SERVER_PID 2>/dev/null || true

  sudo killall policer
  wait $NF_PID 2>/dev/null || true

  sudo ip netns delete lan
  sudo ip netns delete wan
}


make clean
make ADDITIONAL_FLAGS="-DSTOP_ON_RX_0 -g" -j$(nproc)

test_policer 12500 500000

echo "Done."
