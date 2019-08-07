# ===
# This Makefile describes the NF, add the necessary files and command-line arguments here.
# ===

# All non-generated NF files
NF_FILES := main.c config.c

# All structure files whose implementation should be auto-generated
NF_AUTOGEN_SRCS := flow.h

# Arguments used during symbolic execution, benchmarking and running
NF_ARGS := --eth-dest 0,01:23:45:67:89:00 \
           --eth-dest 1,01:23:45:67:89:01



# DO NOT CHANGE - Include parent (in a convoluted way cause of DPDK)
ifeq (dsos, $(MAKECMDGOALS))
include ../Makefile.dsos
else
include $(abspath $(dir $(lastword $(MAKEFILE_LIST))))/../Makefile
endif
