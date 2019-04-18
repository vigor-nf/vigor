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
    sudo taskset -c 8 ./build/policer -n 2 -- --wan 1 --lan 0 \
        --capacity 65536 --rate 375000000 --burst 3750000000 \
else
    echo "[bench] ERROR: non-loopback is not supported" 1>&2
    exit 1
fi
