# All non-generated NF files
NF_FILES := router_main.c config.c

# Arguments used during symbolic execution, benchmarking and running
NF_ARGS := --eth-dest 0,01:23:45:67:89:00 \
           --eth-dest 1,01:23:45:67:89:01

# Layer of the NF in the network stack,
# used for benchmarking to know what levels flows are at
NF_LAYER := 3

# DO NOT CHANGE - Include parent
include $(abspath $(dir $(lastword $(MAKEFILE_LIST))))/../Makefile
