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
# $2: The scenario, see run.sh for details
SCENARIO=$2

if [ -z $MIDDLEBOX ]; then
    echo "[bench] No app specified" 1>&2
    exit 1
fi

if [ -z $SCENARIO ]; then
    echo "[bench] No scenario specified" 1>&2
    exit 2
fi

CLEAN_APP_NAME=`echo "$MIDDLEBOX" | tr '/' '_'`
LOG_FILE="bench-$CLEAN_APP_NAME-$SCENARIO-init.log"

if [ -f "$LOG_FILE" ]; then
    rm "$LOG_FILE"
fi


if [ "$MIDDLEBOX" = "netfilter" -o "$MIDDLEBOX" = "ipvs" ]; then
    case $SCENARIO in
	"latency")
	    EXPIRATION_TIME=1
	    ;;
        "throughput")
            EXPIRATION_TIME=60
            ;;
    esac

    bash ./util/netfilter-short-timeout.sh $EXPIRATION_TIME
else
    echo "[bench] Launching $MIDDLEBOX..."

    EXPIRATION_TIME=60

    case $SCENARIO in
        "latency")
            EXPIRATION_TIME=1000000000 #One second
            ;;
        "throughput")
            EXPIRATION_TIME=60000000000 #One minute
            ;;
        *)
            echo "Unknown scenario $SCENARIO" 1>&2
            exit 10
            ;;
    esac

    # Run the app in the background
    # The arguments are not always necessary, but they'll be ignored if unneeded
    (bash ./bench/run-middlebox.sh "$MIDDLEBOX" \
        "$EXPIRATION_TIME" \
        0<&- &>"$LOG_FILE") &

    # Wait for it to have started
    sleep 20
fi
