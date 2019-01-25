# Binary name
APP := policer

# Runtime and verification files
NF_FILES := policer_main.c policer_config.c policer_data.c

# Verification files
NF_VERIF_FILES := policer_loop.c policer_stub.c

# Verification arguments
NF_VERIF_ARGS := --expire 10 --capacity 100 --config no-file.cfg

# Include parent (in a convoluted way cause of DPDK)
include $(abspath $(dir $(lastword $(MAKEFILE_LIST))))/../Makefile
