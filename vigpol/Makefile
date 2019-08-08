NF_FILES := policer_main.c policer_config.c

NF_AUTOGEN_SRCS := dynamic_value.h ip_addr.h

NF_ARGS := --wan 0 --lan 1 --rate 375000000 --burst 3750000000 --capacity 65536

NF_LAYER := 3

ifeq (dsos, $(MAKECMDGOALS))
include ../Makefile.dsos
else
# Include parent (in a convoluted way cause of DPDK)
include $(abspath $(dir $(lastword $(MAKEFILE_LIST))))/../Makefile
endif
