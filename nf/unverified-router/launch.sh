#!/bin/bash

make router

sudo ./build/router -l 30 --socket-mem=512,512 -w 0000:85:00.1 # --file-prefix pref_router
 

