#!/bin/bash
. ./config.sh

# Parameters:
# $1: The app, either a known name or a folder name containing a DPDK NAT-like app
MIDDLEBOX=$1
# $2: The scenario, see run-middlebox.sh for details
SCENARIO=$2

if [ -z $MIDDLEBOX ]; then
    echo "[bench] No middlebox specified" 1>&2
    exit 1
fi

case $SCENARIO in
    "latency") EXPIRATION_TIME=1;; # we want to measure new flows' latency; see bench.lua for details
    "throughput") EXPIRATION_TIME=60;;
    *) echo "Unknown scenario $SCENARIO" 1>&2; exit 3;;
esac


LOG_FILE="benchmark-$SCENARIO.log"
if [ -f "$LOG_FILE" ]; then
    rm "$LOG_FILE"
fi


if [ "$MIDDLEBOX" = "netfilter" -o "$MIDDLEBOX" = "ipvs" ]; then
    ./util/netfilter-short-timeout.sh $EXPIRATION_TIME
else
    # convert s to us
    export EXPIRATION_TIME="$(echo "$EXPIRATION_TIME * 1000 * 1000" | bc)"

    pushd $MIDDLEBOX >> /dev/null
        echo "[bench] Running $MIDDLEBOX..."
        NF_DPDK_ARGS="-l $MB_CPU -n 2" make run > "$LOG_FILE" 2>&1 &
    popd >> /dev/null

    # Wait for it to have started
    sleep 20
fi
