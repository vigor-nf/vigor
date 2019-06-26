#!/bin/bash
. ./config.sh

echo "[clean] Cleaning machines..."
ssh $TESTER_HOST "~/scripts/clean/tester.sh"
./clean/middlebox.sh
