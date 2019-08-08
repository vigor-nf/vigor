NF_FILES := router.c parse_utils.c

NF_LAYER := 3

# Include parent (in a convoluted way cause of DPDK)
NF_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))
include $(NF_DIR)/../Makefile.common
