#!/bin/bash
. ./config.sh

# Parameters:
# $1: The app, either a known name or a folder name containing a DPDK NAT-like app
MIDDLEBOX=$1
# $2: The scenario, see run-middlebox.sh for details
SCENARIO=$2
# $3: The type of NF, see bench.sh for details
NF_TYPE=$3

if [ -z $MIDDLEBOX ]; then
    echo "[bench] No middlebox specified" 1>&2
    exit 1
fi

CLEAN_APP_NAME=`echo "$MIDDLEBOX" | tr '/' '_'`
LOG_FILE="$(realpath "bench-$CLEAN_APP_NAME-$SCENARIO.log")"

if [ -f "$LOG_FILE" ]; then
    rm "$LOG_FILE"
fi

case $SCENARIO in
    "latency") EXPIRATION_TIME=1;;
    "throughput") EXPIRATION_TIME=60;;
    *) echo "Unknown scenario $SCENARIO" 1>&2; exit 3;;
esac

if [ "$MIDDLEBOX" = "netfilter" -o "$MIDDLEBOX" = "ipvs" ]; then
    ./util/netfilter-short-timeout.sh $EXPIRATION_TIME
else
    EXPIRATION_TIME="$(echo "$EXPIRATION_TIME * 1000 * 1000 * 1000" | bc)"

    ETH_DEST=0 # whether we should append the --eth-dest stuff
    case $NF_TYPE in
        "NAT") ETH_DEST=1; ARGS="--lan-dev 1 --max-flows 65535 --starting-port 1 --extip $MB_IP_EXTERNAL --expire $EXPIRATION_TIME";;
        "Br") ARGS="--capacity 65536 --expire $EXPIRATION_TIME";;
        "LB") ARGS="--flow-capacity 65536 --flow-expiration $EXPIRATION_TIME --cht-height 97 --backend-capacity 20 --backend-expiration 60000000000";;
        "Pol") ARGS='--wan 1 --lan 0 --capacity 65536 --rate 375000000 --burst 3750000000';;
        "FW") ETH_DEST=1; ARGS="--wan 0 --max-flows 65536 --expire $EXPIRATION_TIME";;
        "NOP") ETH_DEST=1; ARGS='--wan 0 --lan-dev 1';;
        *) echo "Unknown NF type $NF_TYPE" 1>&2; exit 4;;
    esac

    if [ $ETH_DEST -eq 1 ]; then
        ARGS="$ARGS --eth-dest 0,$TESTER_MAC_EXTERNAL --eth-dest 1,$TESTER_MAC_INTERNAL"
    fi

    pushd $MIDDLEBOX >> /dev/null
        echo "[bench] Building $MIDDLEBOX..."
        make clean > "$LOG_FILE"
        make >> "$LOG_FILE"

        echo "[bench] Running $MIDDLEBOX..."
        sudo ./build/nf -l 8 -n 2 -- $ARGS >> "$LOG_FILE" 2>&1 &
    popd >> /dev/null

    # Wait for it to have started
    sleep 20
fi
