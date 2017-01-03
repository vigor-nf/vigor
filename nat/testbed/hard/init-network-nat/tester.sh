#!/bin/bash
. ~/scripts/config.sh

echo "[init] Initializing DPDK on tester..."
. ~/scripts/util/dpdk-functions.sh
set_numa_pages
load_igb_uio_module

echo "[init] Binding TESTER_DEVICE_EXTERNAL to DPDK..."
sudo ifconfig $TESTER_DEVICE_EXTERNAL down
bind_nics_to_igb_uio $TESTER_PCI_EXTERNAL


echo "[init] Unbinding TESTER_PCI_INTERNAL from DPDK..."
$RTE_SDK/tools/dpdk-devbind.py -b igb $TESTER_PCI_INTERNAL
sleep 10

echo "[init] Configuring tester IP..."
ifconfig $TESTER_DEVICE_INTERNAL up
ip addr flush dev $TESTER_DEVICE_INTERNAL
ip addr add $TESTER_IP_INTERNAL/24 dev $TESTER_DEVICE_INTERNAL

echo "[init] Configuring tester route..."
ip route flush $SERVER_SUBNET
ip route add $SERVER_SUBNET/24 via $MB_IP_INTERNAL dev $TESTER_DEVICE_INTERNAL
ip route flush cache
arp -s $MB_IP_INTERNAL $MB_MAC_INTERNAL

echo "[init] Configuring tester connection reuse speed..."
. ~/scripts/util/relieve-connection-reuse.sh