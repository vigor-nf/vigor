#!/bin/bash
. ./config.sh

echo "[clean] Unbinding middlebox interfaces from Linux..."
sudo ifconfig $MB_DEVICE_INTERNAL down
sudo ifconfig $MB_DEVICE_EXTERNAL down
sudo ifconfig $MB_DEVICE_TO_SRV down

echo "[clean] Unbinding middlebox interfaces from DPDK..."
if [ -f "$RTE_SDK/.version" ] && [ "$(cat $RTE_SDK/.version)" = "17.11" ]; then
  sudo ${RTE_SDK}/usertools/dpdk-devbind.py -b $KERN_NIC_DRIVER $MB_PCI_INTERNAL $MB_PCI_EXTERNAL $MB_PCI_TO_SRV && echo "OK"
else
  sudo ${RTE_SDK}/usertools/dpdk-devbind.py -b $KERN_NIC_DRIVER $MB_PCI_INTERNAL $MB_PCI_EXTERNAL $MB_PCI_TO_SRV && echo "OK"
fi

echo "[clean] Killing middlebox..."
sudo killall -9 nat lb bridge policer click fw nop
