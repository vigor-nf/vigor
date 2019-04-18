#!/bin/bash


# Runs VigNAT for a specified scenario

# Parameters:
# $1: The scenario: can be "loopback" or "rr"
# $2: Config file 
# $3: Expiration time for flows (Hack)

SCENARIO=$1
CONFIG_FILE=$2
EXP_TIME=$3

. $CONFIG_FILE
set -x 
# List of config variables for NAT to run - see lib/nat_config.c 

if [ $SCENARIO = "loopback" ]; then
    sudo taskset -c 8 ./build/nat -n 2 -- --wan 0 --lan-dev 1 \
        --max-flows 65536 --starting-port 1 \
	--extip $MB_IP_EXTERNAL \
        --eth-dest 0,$TESTER_MAC_EXTERNAL --eth-dest 1,$TESTER_MAC_INTERNAL \
	--expire $EXP_TIME
else
    echo "[bench] ERROR: non-loopback is not supported" 1>&2
    exit 1
fi
