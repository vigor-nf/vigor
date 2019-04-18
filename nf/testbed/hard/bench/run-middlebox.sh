#!/bin/bash
. ./config.sh

# Runs a DPDK app for the specified scenario

# Parameters:
# $1: Scenario, can be "loopback" or "rr"
# $2: Folder of the app; the app must be named "nat"
#     and take the usual arguments e.g. "--extip"
# $3: Additional parameters for the NF

SCENARIO=$1
MIDDLEBOX=$2
PARAMS=$3
CONFIG=$(realpath config.sh)

pushd $MIDDLEBOX >> /dev/null

   echo "[bench] Building $MIDDLEBOX..."
   sudo rm build -rf
   make clean
   make
  
   echo "[bench] Running $MIDDLEBOX..."
   if [ ! -f run.sh ]; then 
	   echo "Cannot find run file for Middlebox:$MIDDLEBOX"
   else
           bash run.sh $SCENARIO $CONFIG "$PARAMS" #Params is hacky here, but ehh
   fi
 
popd >> /dev/null
