#!/bin/bash
. ./config.sh

echo "[init] Cloning scripts..."
rsync -a -q --exclude '*.log' --exclude '*.results' ./ "$TESTER_HOST:scripts"

echo "[init] Initializing all machines..."
ssh "$TESTER_HOST" '~/scripts/init-machines/tester.sh'
./init-machines/middlebox.sh
