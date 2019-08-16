#!/bin/bash
. ./config.sh

# Master script to run the prepared benchmarks for Vigor-related programs.

# Parameters:
# $1: Path to the NF
MIDDLEBOX=$1
# $2: The scenario, one of the following:
#     "throughput": Measure throughput, find the rate at which the middlebox
#                                       starts losing 0.1% of packets.
#     "latency": Measure the forwarding latency for existing flows.
SCENARIO=$2
# $3: Results file
RESULTS_FILE=$3

if [ -z $MIDDLEBOX ]; then
    echo "[run] No scenario specified" 1>&2
    exit 1
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
pushd $MIDDLEBOX >> /dev/null
  # Without -s, make prints 'Entering directory..' messages, idk why
  LAYER="$(make -s _print-layer)"
  if [ "$(make -s _print-needsreverse)" = "true" ]; then EXTRA='-x 32'; fi
popd >> /dev/null

case $SCENARIO in
    "latency") DURATION=60;; # few probe flows per second so we need longer benchmarks
    "throughput") DURATION=60;;
    *) echo "Unknown scenario $SCENARIO" 1>&2; exit 5;;
esac

echo "[bench] Benchmarking..."
ssh $TESTER_HOST "sudo ~/moon-gen/build/MoonGen ~/scripts/bench.lua -p 60 -d $DURATION $EXTRA $SCENARIO $LAYER 0 1"
scp $TESTER_HOST:results.tsv "./$RESULTS_FILE"
