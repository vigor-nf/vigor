#!/bin/bash
. ./config.sh

# Runs a DPDK app for the specified scenario

# Parameters:
# $1: Folder of the app; the app must be named "nat"
#     and take the usual arguments e.g. "--extip"
# $2: Additional parameters for the NF

MIDDLEBOX=$1
PARAMS=$2
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
           bash run.sh "$CONFIG" "$PARAMS"
   fi
popd >> /dev/null
