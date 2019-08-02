#!/bin/bash

set -euo pipefail

if [ -z "${1:-}" ]; then
  echo "Usage: $(basename $0) <boot image>"
  exit 1
fi
BOOT_IMG="$(realpath ${1:-})"

PXE_NIC="em4"
PXE_SERVER_IP="192.168.0.254"
PXE_NETWORK_MASK="255.255.255.0"
PXE_CLIENT_IP_FIRST="192.168.0.1"
PXE_CLIENT_IP_LAST="192.168.0.253"
IPXE_IMG="/usr/lib/ipxe/undionly.kpxe"

if [ ! -f "$IPXE_IMG" ]; then
  echo "iPXE not found."
  exit 1
fi

TFTP_DIR="$(mktemp -d)"
ln -s $IPXE_IMG $TFTP_DIR
ln -s $BOOT_IMG $TFTP_DIR

sudo ifconfig $PXE_NIC $PXE_SERVER_IP netmask $PXE_NETWORK_MASK up

function cleanup {
  echo "Cleaning up."
  rm -rf "$TFTP_DIR"
}
trap cleanup EXIT

echo "Running DHCP/BootP server. Press Ctrl-C when done."
sudo dnsmasq -k -d -l /dev/null -R -h -i $PXE_NIC --bind-dynamic \
             --dhcp-range=$PXE_CLIENT_IP_FIRST,$PXE_CLIENT_IP_LAST,$PXE_NETWORK_MASK,5m \
             --dhcp-userclass=set:ipxe,iPXE \
             --dhcp-boot $(basename $IPXE_IMG) \
             --dhcp-boot tag:ipxe,$(basename $BOOT_IMG) \
             --enable-tftp --tftp-root $TFTP_DIR
