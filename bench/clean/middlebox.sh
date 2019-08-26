#!/bin/bash
. ./config.sh

# $1: The middlebox path (so we know what to kill)
MIDDLEBOX=$1

if [ -z "$MIDDLEBOX" ]; then
  echo 'No middlebox given to clean'
  exit 1
fi

echo "[clean] Killing middlebox..."
pushd $MIDDLEBOX >> /dev/null
  sudo killall -SIGKILL $(make -s _print-processname) > /dev/null 2>&1
popd >> /dev/null
