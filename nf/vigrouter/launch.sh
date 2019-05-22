#!/bin/bash

make router

sudo ./build/router -l 30 --socket-mem=1024,1024 -w 0000:83:00.0 
 

