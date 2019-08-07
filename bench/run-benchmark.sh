#!/bin/bash
. ./config.sh

# Master script to run the prepared benchmarks for Vigor-related programs.

# Parameters:
# $1: The scenario, one of the following:
#     "throughput": Measure throughput, find the rate at which the middlebox
#                                       starts losing 0.1% of packets.
#     "latency": Measure the forwarding latency for existing flows.
SCENARIO=$1
# $3: NF type, one of NAT/FW/NOP/LB/Pol/Br
NF_TYPE=$2
# $4: Results file
RESULTS_FILE=$3

if [ -z $SCENARIO ]; then
    echo "[run] No scenario specified" 1>&2
    exit 2
fi

if [ -z $RESULTS_FILE ]; then
    echo "[bench] No results file specified" 1>&2
    exit 3
fi

if [ -f "$RESULTS_FILE" ]; then
    echo "[run] results file exists! exiting" 1>&2
    exit 4
fi


EXTRA=''
case $NF_TYPE in
    "Br") LAYER=2;;
    "LB") LAYER=3; EXTRA='-x 20';; # LB needs reverse traffic to populate backends
    "Pol") LAYER=3;;
    "NAT"|"FW"|"NOP") LAYER=4;;
    *) echo "[bench] Unknown NF type: $NF_TYPE" 1>&2; exit 5
esac

echo "[bench] Benchmarking..."
ssh $TESTER_HOST "sudo ~/moon-gen/build/MoonGen ~/scripts/bench.lua -p 60 -d 10 $EXTRA $SCENARIO $LAYER 1 0"
scp $TESTER_HOST:results.tsv "./$RESULTS_FILE"
