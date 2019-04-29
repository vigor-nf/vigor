#!/bin/bash
. ./config.sh

MIDDLEBOX=$1

if [ -z $MIDDLEBOX ]; then
    echo "[bench] No app specified" 1>&2
    exit 1
fi

if [ "$MIDDLEBOX" = "netfilter" -o "$MIDDLEBOX" = "ipvs" ]; then
    echo "no need to kill netfilter"
else
    sudo killall -9 nat lb bridge policer click fw nop
fi
