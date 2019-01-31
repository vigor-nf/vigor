# Binary name
APP := policer

# Runtime and verification files
NF_FILES := policer_main.c policer_config.c policer_data.c

# Verification files
NF_VERIF_FILES := policer_loop.c policer_stub.c

# Verification arguments
NF_VERIF_ARGS := --lan 0 --wan 1 --rate 12500 125000 --capacity 100

# Include parent (in a convoluted way cause of DPDK)
include $(abspath $(dir $(lastword $(MAKEFILE_LIST))))/../Makefile
