#!/bin/bash
. ./config.sh

echo "[clean] Killing middlebox..."
sudo killall -9 nf > /dev/null 2>&1
