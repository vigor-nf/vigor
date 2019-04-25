#!/bin/bash

# Parameter which decides which NFs must be run. Can be either "Vigor" or "Baselines" or "All"
NF_LIST=$1 

# Initialize the machines, i.e. software+scripts
. ./init-machines.sh
# Clean first, just in case
. ./clean.sh

VNDS_PREFIX="$HOME/projects/Vigor/vnds/nf"
CLICK_PREFIX="$HOME/projects/Vigor/fastclick/conf/vnds-baselines"
NOW=$(date +"%d.%m.%Y_%H_%M")


case $NF_LIST in 
	"Vigor")
		MIDDLEBOXES=("$VNDS_PREFIX/vignat" "$VNDS_PREFIX/vigbridge" "$VNDS_PREFIX/unverified-nop" "$VNDS_PREFIX/vigbalancer" "$VNDS_PREFIX/vigpolicer" "$VNDS_PREFIX/vigfw" )
		;;
	
	"Baselines")
		MIDDLEBOXES=("$CLICK_PREFIX/click-nat" "$CLICK_PREFIX/click-nop" "$CLICK_PREFIX/click-bridge" "$CLICK_PREFIX/click-fw" "$CLICK_PREFIX/click-lb" )
		;;
		
	"All")
		MIDDLEBOXES=("$VNDS_PREFIX/vignat" "$VNDS_PREFIX/vigbridge" "$VNDS_PREFIX/unverified-nop" "$VNDS_PREFIX/vigbalancer" "$VNDS_PREFIX/vigpolicer" "$VNDS_PREFIX/vigfw" "$CLICK_PREFIX/click-nat" "$CLICK_PREFIX/click-nop" "$CLICK_PREFIX/click-bridge" "$CLICK_PREFIX/click-fw" "$CLICK_PREFIX/click-lb" )
		;;
	*)
		echo "[bench] Unknown parameter passed. Please pass one of Vigor/Baselines/All"
	        exit 1
		;;
esac	

SCENARIOS=("mg-new-flows-latency" "mg-1p")
declare -A NF_TYPES
NF_TYPES[$VNDS_PREFIX/vignat]=NAT
NF_TYPES[$VNDS_PREFIX/vigbridge]=Br
NF_TYPES[$VNDS_PREFIX/vigbalancer]=LB
NF_TYPES[$VNDS_PREFIX/vigpolicer]=Pol
NF_TYPES[$VNDS_PREFIX/vigfw]=FW
NF_TYPES[$VNDS_PREFIX/unverified-nop]=NOP
NF_TYPES[$CLICK_PREFIX/click-nat]=NAT
NF_TYPES[$CLICK_PREFIX/click-bridge]=Br
NF_TYPES[$CLICK_PREFIX/click-nop]=NOP
NF_TYPES[$CLICK_PREFIX/click-fw]=FW
NF_TYPES[$CLICK_PREFIX/click-lb]=LB


mkdir -p $NOW

for MIDDLEBOX in ${MIDDLEBOXES[@]}; do
    # The second parameter should not matter (it doesn't for mg-* scenarios,
    # but unfortunately it does for the old ones, so to not try this for those)
    . ./init.sh $MIDDLEBOX "mg-1p"
    NF_TYPE=${NF_TYPES[$MIDDLEBOX]}
    if [ -z $NF_TYPE ]; then
	    echo "[bench] NF_TYPE unspecified for $MIDDLEBOX"
	    exit 1
    fi

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
