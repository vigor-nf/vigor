#!/bin/bash
. ./config.sh

# Master script to benchmark VigNAT-related programs.
# Can benchmark different implementations, including non-NATs,
# using different scenarios.

# Parameters:
# $1: The app, either a known name or a DPDK NAT-like app.
#     Known names: "netfilter".
#     Otherwise, a folder name containing a DPDK NAT-like app, e.g. "~/vnds/nat"
# $2: The scenario, see run.sh for details
# $3: The type of NF, either NAT/Br/LB/Pol/FW/NOP
#     For running programs such as netfilter please provide the NF it is being used as a baseline for:.

MIDDLEBOX=$1
SCENARIO=$2
NF_TYPE=$3

if [ -z $MIDDLEBOX ]; then
    echo "[bench] No app specified" 1>&2
    exit 1
fi

if [ -z $SCENARIO ]; then
    echo "[bench] No scenario specified" 1>&2
    exit 2
fi

if [ -z $NF_TYPE ]; then 
    echo "[bench] NF Type not specified " 1>&2
    exit 3
fi

CLEAN_APP_NAME=`echo "$MIDDLEBOX" | tr '/' '_'`
RESULTS_FILE="bench-$CLEAN_APP_NAME-$SCENARIO.results"

if [ -f "$RESULTS_FILE" ]; then
    rm "$RESULTS_FILE"
fi


# Initialize the machines, i.e. software+scripts
. ./init-machines.sh

# Clean first, just in case
. ./clean.sh

. init.sh $MIDDLEBOX

. start-middlebox.sh $MIDDLEBOX $SCENARIO

. run.sh $SCENARIO $NF_TYPE $RESULTS_FILE

. stop-middlebox.sh $MIDDLEBOX

. clean.sh
