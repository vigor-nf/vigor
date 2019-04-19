#!/bin/bash

# Initialize the machines, i.e. software+scripts
. ./init-machines.sh
# Clean first, just in case
. ./clean.sh

VNDS_PREFIX="$HOME/projects/Vigor/vnds/nf"

NOW=$(date +"%d.%m.%Y_%H_%M")

MIDDLEBOXES=("$VNDS_PREFIX/vignat" "$VNDS_PREFIX/vigbridge" "$VNDS_PREFIX/unverified-nop" "$VNDS_PREFIX/vigbalancer" "$VNDS_PREFIX/vigpolicer" "$VNDS_PREFIX/vigfw")
SCENARIOS=("mg-new-flows-latency" "mg-1p")
declare -A NF_TYPES
NF_TYPES[$VNDS_PREFIX/vignat]=NAT
NF_TYPES[$VNDS_PREFIX/vigbridge]=Br
NF_TYPES[$VNDS_PREFIX/vigbalancer]=LB
NF_TYPES[$VNDS_PREFIX/vigpolicer]=Pol
NF_TYPES[$VNDS_PREFIX/vigfw]=FW
NF_TYPES[$VNDS_PREFIX/unverified-nop]=NOP


mkdir -p $NOW

for MIDDLEBOX in ${MIDDLEBOXES[@]}; do
    # The second parameter should not matter (it doesn't for mg-* scenarios,
    # but unfortunately it does for the old ones, so to not try this for those)
    . ./init.sh $MIDDLEBOX "mg-1p"
    NF_TYPE=${NF_TYPES[$MIDDLEBOX]}

    for SCENARIO in ${SCENARIOS[@]}; do
	echo "Benching Middlebox $MIDDLEBOX in Scenario $SCENARIO"
        . ./start-middlebox.sh $MIDDLEBOX $SCENARIO
        CLEAN_APP_NAME=`echo "$MIDDLEBOX" | tr '/' '_'`
        RESULTS_FILE="$NOW/$CLEAN_APP_NAME-$SCENARIO.results"
        . ./run.sh $MIDDLEBOX $SCENARIO $NF_TYPE  $RESULTS_FILE
        . ./stop-middlebox.sh $MIDDLEBOX
    done
done

. ./clean.sh
