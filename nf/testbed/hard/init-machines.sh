#!/bin/bash
. ./config.sh

echo "[init] Cloning scripts..."
for h in $TESTER_HOST; do
    rsync -q -t -r --exclude '*.log' --exclude '*.results' ./ $h:scripts
done

echo "[init] Initializing all machines..."
ssh $TESTER_HOST 'bash ~/scripts/init-machines/tester.sh'
. ./init-machines/middlebox.sh
