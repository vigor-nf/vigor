# Runtime and verification files
NF_FILES := bridge_main.c bridge_config.c

# Auto-generation sources
NF_AUTOGEN_SRCS := dyn_value.h stat_key.h

# Verification arguments
NF_VERIF_ARGS := --expire 10 --capacity 100 --config no-file.cfg

# Include parent (in a convoluted way cause of DPDK)
include $(abspath $(dir $(lastword $(MAKEFILE_LIST))))/../Makefile
