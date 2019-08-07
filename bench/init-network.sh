#!/bin/bash
. ./config.sh

# Initializes the network for the specified scenario and app,
# by running the appropriate scripts on all three machines.


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

if [ ! -d ./init-network/$NETWORK_APP ]; then
    echo "[init] Error, unknown app specified in init-network" 1>&2
    exit 4
fi

ssh "$TESTER_HOST" "~/scripts/init-network/tester.sh"

./init-network/$NETWORK_APP/middlebox.sh
