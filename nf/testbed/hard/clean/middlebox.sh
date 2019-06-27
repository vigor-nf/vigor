#!/bin/bash
. ./config.sh

echo "[clean] Killing middlebox..."
sudo killall -9 nf
