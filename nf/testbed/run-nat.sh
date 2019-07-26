#!/bin/bash

EXPTIME=300000000 # nanoseconds
MAX_FLOWS=65535

if [ -z $EXPTIME ]; then
    EXPTIME=10
fi

if [ -z $MAX_FLOWS ]; then
    MAX_FLOWS=1024
fi

sudo /nat/vignat/build/nf -c 0x01 -n 2 -- --wan 0 --lan-dev 1 --expire $EXPTIME --max-flows $MAX_FLOWS --starting-port 1025  --extip 192.168.33.2 --eth-dest 0,08:00:27:53:8b:38 --eth-dest 1,08:00:27:c1:13:47

