

#Enables compilation of test program
TESTING = yes

ifeq ($(TESTING),no)

#version like unverified-nat

include $(RTE_SDK)/mk/rte.vars.mk

# binary name
APP = router

# sources
SRCS-y := router.c parse_utils.c \
          ../nf_main.c \
          ../lib/nf_time.c \
          ../lib/containers/double-chain-impl.c \
          ../lib/containers/double-chain.c \
          ../lib/containers/lpm_trie.c \
    

# gcc flags
CFLAGS += -O3
CFLAGS += -I.. -I../..
CFLAGS += -std=c99
CFLAGS += -DNORMAL

# disable warnings triggered by DPDK
CFLAGS += -Wno-implicit-function-declaration
CFLAGS += -Wno-nested-externs

include $(RTE_SDK)/mk/rte.extapp.mk




#version for tests
else


CFLAGS=-W -Wall -std=c99 -pedantic 


all: tests 


tests: tests.o parse_utils.o math_utils.o router.o ../lib/containers/lpm_trie.o ../lib/containers/double-chain-impl.o ../lib/containers/double-chain.o ../lib/nf_time.o
	gcc -o tests tests.o parse_utils.o math_utils.o router.o ../lib/containers/lpm_trie.o ../lib/containers/double-chain-impl.o ../lib/containers/double-chain.o  ../lib/nf_time.o $(CFLAGS) -DTEST

tests.o: tests.c parse_utils.h math_utils.h router.h ../lib/containers/lpm_trie_mem.h ../lib/nf_time.h
	gcc -o tests.o -c tests.c $(CFLAGS) -DTEST

router.o: router.c ../lib/containers/lpm_trie_mem.h parse_utils.h router.h 
	gcc -o router.o -c router.c $(CFLAGS) -DTEST

parse_utils.o: parse_utils.c parse_utils.h math_utils.h
	gcc -o parse_utils.o -c parse_utils.c $(CFLAGS)

math_utils.o: math_utils.c math_utils.h
	gcc -o math_utils.o -c math_utils.c $(CFLAGS)

../lib/containers/lpm_trie.o: ../lib/containers/lpm_trie.c ../lib/containers/double-chain.h
	gcc -o ../lib/containers/lpm_trie.o -c ../lib/containers/lpm_trie.c $(CFLAGS)

../lib/containers/double-chain.o: ../lib/containers/double-chain.c ../lib/containers/double-chain-impl.h
	gcc -o ../lib/containers/double-chain.o -c ../lib/containers/double-chain.c $(CFLAGS)

../lib/containers/double-chain-impl.o: ../lib/containers/double-chain-impl.c
	gcc -o ../lib/containers/double-chain-impl.o -c ../lib/containers/double-chain-impl.c $(CFLAGS)

../lib/nf_time.o: ../lib/nf_time.c
	gcc -o ../lib/nf_time.o -c ../lib/nf_time.c $(CFLAGS)


# Include parent (in a convoluted way cause of DPDK)
#include $(abspath $(dir $(lastword $(MAKEFILE_LIST))))/../Makefile



endif
