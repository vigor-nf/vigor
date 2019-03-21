CFLAGS = -std=c11
CFLAGS += -Wall

all: tests

tests: tests.o rte_lpm.o

tests.o: tests.c rte_lpm.h

rte_lpm.o: rte_lpm.c rte_lpm.h

# Include parent (in a convoluted way cause of DPDK)
include $(abspath $(dir $(lastword $(MAKEFILE_LIST))))/../Makefile