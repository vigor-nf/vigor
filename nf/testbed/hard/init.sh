#!/bin/bash
. ./config.sh

# Master script to initialize VigNAT-related programs benchmarks.
# Can work with different implementations, including non-NATs,
# using different scenarios.

# Parameters:
# $1: The app, either a known name or a DPDK NAT-like app.
#     Known names: "netfilter".
#     Otherwise, a folder name containing a DPDK NAT-like app

MIDDLEBOX=$1

if [ -z $MIDDLEBOX ]; then
    echo "[bench] No app specified" 1>&2
    exit 1
fi

NETWORK_APP="dpdk"
if [ $MIDDLEBOX = "netfilter" ]; then
    NETWORK_APP="netfilter"
elif [ $MIDDLEBOX = "ipvs" ]; then
    NETWORK_APP="ipvs"
elif [ ! -d $MIDDLEBOX ]; then
    echo "Unknown middlebox app: $MIDDLEBOX" 1>&2
    exit 10
fi

. ./init-network.sh $NETWORK_APP
