NF_FILES := policer_main.c policer_config.c

NF_AUTOGEN_SRCS := dynamic_value.h ip_addr.h

NF_ARGS := --lan 0 --wan 1 --rate 12500 --burst 125000 --capacity 100

ifeq (dsos, $(MAKECMDGOALS))
include ../Makefile.dsos
else
# Include parent (in a convoluted way cause of DPDK)
include $(abspath $(dir $(lastword $(MAKEFILE_LIST))))/../Makefile
endif
