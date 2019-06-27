#!/bin/bash
. ~/scripts/config.sh

echo "[init] Initializing DPDK on tester..."
. ~/scripts/util/dpdk-functions.sh
set_numa_pages
load_igb_uio_module

echo "[init] Binding tester interfaces to DPDK..."
for pci in "$TESTER_PCI_INTERNAL" "$TESTER_PCI_EXTERNAL"; do
  if sudo "$RTE_SDK/usertools/dpdk-devbind.py" --status | grep -F "$pci" | grep -q "drv=$KERN_NIC_DRIVER"; then
    sudo "$RTE_SDK/usertools/dpdk-devbind.py" --bind "$DPDK_NIC_DRIVER" "$pci"
  fi
done
