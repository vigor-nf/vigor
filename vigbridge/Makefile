NF_FILES := bridge_main.c bridge_config.c

NF_AUTOGEN_SRCS := dyn_value.h stat_key.h

NF_ARGS := --expire 10 --capacity 100 --config no-file.cfg

ifeq (dsos, $(MAKECMDGOALS))
include ../Makefile.dsos
else
# Include parent (in a convoluted way cause of DPDK)
include $(abspath $(dir $(lastword $(MAKEFILE_LIST))))/../Makefile
endif
