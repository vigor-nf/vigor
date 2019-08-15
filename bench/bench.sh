#!/bin/bash
. ./config.sh

# Master script to benchmark VigNAT-related programs.
# Can benchmark different implementations, including non-NATs,
# using different scenarios.

# Parameters:
# $1: The app, either a known name or a DPDK NAT-like app.
#     Known names: "netfilter", "ipvs".
#     Otherwise, a folder name containing a DPDK NAT-like app, e.g. "/home/solal/vnds/vignat"
# $2: The scenario, see run-benchmark.sh for details

MIDDLEBOX=$1
SCENARIO=$2

if [ -z $MIDDLEBOX ]; then
    echo "[bench] No app specified" 1>&2
    exit 1
fi

if [ -z $SCENARIO ]; then
    echo "[bench] No scenario specified" 1>&2
    exit 2
fi


RESULTS_FILE="benchmark-$SCENARIO.results"
if [ -f "$RESULTS_FILE" ]; then
    rm "$RESULTS_FILE"
fi


./init-machines.sh
./clean.sh $MIDDLEBOX
./init-network.sh $MIDDLEBOX
./run-middlebox.sh $MIDDLEBOX $SCENARIO
./run-benchmark.sh $MIDDLEBOX $SCENARIO $RESULTS_FILE
./clean.sh $MIDDLEBOX
