#!/bin/bash
. ./config.sh

# Initializes the network for the specified scenario and app,
# by running the appropriate scripts on all three machines.

# Parameters:
# $1: App; there must exist a folder "init-network/$1",
#     with a "middlebox.sh" script.

if [ -z $1 ]; then
    echo "[init] Error, no app specified in init-network" 1>&2
    exit 3
fi

if [ ! -d ./init-network/$1 ]; then
    echo "[init] Error, unknown app specified in init-network" 1>&2
    exit 4
fi

ssh $TESTER_HOST "bash ~/scripts/init-network/tester.sh"

. ./init-network-$1/middlebox.sh
