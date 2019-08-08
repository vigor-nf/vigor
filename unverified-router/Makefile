NF_FILES := router.c parse_utils.c

NF_LAYER := 3

# Include parent (in a convoluted way cause of DPDK)
include $(abspath $(dir $(lastword $(MAKEFILE_LIST))))/../Makefile
