#!/bin/bash
. ./config.sh
. ./util/functions.sh

echo "[init] Configuring middlebox IPs..."
sudo ifconfig $MB_DEVICE_EXTERNAL up
sudo ip addr flush dev $MB_DEVICE_EXTERNAL
sudo ip addr add $MB_IP_EXTERNAL/24 dev $MB_DEVICE_EXTERNAL
sudo ifconfig $MB_DEVICE_INTERNAL up
sudo ip addr flush dev $MB_DEVICE_INTERNAL
sudo ip addr add $MB_IP_INTERNAL/24 dev $MB_DEVICE_INTERNAL
sudo ifconfig $MB_DEVICE_TO_SRV down

echo "[init] Configuring middlebox forwarding rules..."
sudo sysctl -w net.ipv4.ip_forward=1
sudo_append /etc/sysctl.conf "net.ipv4.ip_forward=1"

sudo ipvsadm -A -u $MB_IP_INTERNAL:5001 -s lc
for BACKEND_IP in $MB_IPS_BACKENDS=; do \
  sudo ipvsadm -a -u $MB_IP_INTERNAL:5001 -r $BACKEND_IP:5001 -m
done

sudo arp -s $TESTER_IP_EXTERNAL $TESTER_MAC_EXTERNAL
sudo arp -s $TESTER_IP_INTERNAL $TESTER_MAC_INTERNAL

echo "[init] Unlocking software restrictions on middlebox NetFilter..."
. ./util/netfilter-unlock.sh $MB_DEVICE_EXTERNAL
