#!/bin/bash
. ./config.sh

echo "[init] Initializing DPDK on middlebox..."
. ./util/dpdk-functions.sh
set_numa_pages
load_igb_uio_module

echo "[init] Binding middlebox interfaces to DPDK..."
for pci in "$MB_PCI_INTERNAL" "$MB_PCI_EXTERNAL"; do
  if sudo "$RTE_SDK/usertools/dpdk-devbind.py" --status | grep -F "$pci" | grep -q "drv=$KERN_NIC_DRIVER"; then
    sudo "$RTE_SDK/usertools/dpdk-devbind.py" --bind "$DPDK_NIC_DRIVER" "$pci"
  fi
done
