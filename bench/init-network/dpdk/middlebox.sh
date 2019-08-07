#!/bin/bash
. ./config.sh

echo "[init] Binding middlebox interfaces to DPDK..."
LOADED_DPDK=0
for pci in "$MB_PCI_INTERNAL" "$MB_PCI_EXTERNAL"; do
  if ! sudo "$RTE_SDK/usertools/dpdk-devbind.py" --status | grep -F "$pci" | grep -q "drv=$DPDK_NIC_DRIVER"; then
    if [ $LOADED_DPDK -eq 0 ]; then
      echo "[init] Initializing DPDK on middlebox..."
      . ./util/dpdk-functions.sh
      set_numa_pages
      load_igb_uio_module
      LOADED_DPDK=1
    fi

    sudo "$RTE_SDK/usertools/dpdk-devbind.py" --force --bind "$DPDK_NIC_DRIVER" "$pci"
  fi
done
