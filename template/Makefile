# ===
# This Makefile describes the NF,
# add the necessary files and command-line arguments here.
# ===

# All non-generated NF files
NF_FILES := main.c config.c

# All structure files whose implementation should be auto-generated
NF_AUTOGEN_SRCS := flow.h

# Arguments used during symbolic execution, benchmarking and running
NF_ARGS := --eth-dest 0,01:23:45:67:89:00 \
           --eth-dest 1,01:23:45:67:89:01

# Layer of the NF in the network stack,
# used for benchmarking to know what levels flows are at
NF_LAYER := 2

# `true` if the NF needs some reverse traffic for a benchmark to be meaningful
# (e.g. Maglev needs backend heartbeats)
NF_BENCH_NEEDS_REVERSE_TRAFFIC := false

# DO NOT CHANGE - Include parent
include $(abspath $(dir $(lastword $(MAKEFILE_LIST))))/../Makefile
