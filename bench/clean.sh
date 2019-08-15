#!/bin/bash
. ./config.sh

# $1: The middlebox path (so we know what to kill)

echo "[clean] Cleaning machines..."
ssh $TESTER_HOST "~/scripts/clean/tester.sh"
./clean/middlebox.sh $1
