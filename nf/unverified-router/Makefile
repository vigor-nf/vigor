
#test version

ifeq ("0","1")

#compilation flags
CFLAGS=-W -Wall -std=c11 -pedantic 



all: tests 


tests: tests.o parse_utils.o math_utils.o router.o lpm_trie/lpm_trie.o lpm_trie/lib/double-chain-impl.o lpm_trie/lib/double-chain.o nf_time.o
	gcc -o tests tests.o parse_utils.o math_utils.o router.o lpm_trie/lpm_trie.o lpm_trie/lib/double-chain-impl.o lpm_trie/lib/double-chain.o nf_time.o
	
tests.o: tests.c parse_utils.h math_utils.h router.h nf_time.h
	gcc -o tests.o -c tests.c $(CFLAGS)

router.o: router.c lpm_trie/lpm_trie_mem.h parse_utils.h router.h nf_time.h
	gcc -o router.o -c router.c $(CFLAGS)

parse_utils.o: parse_utils.c parse_utils.h math_utils.h
	gcc -o parse_utils.o -c parse_utils.c $(CFLAGS)
	
math_utils.o: math_utils.c math_utils.h
	gcc -o math_utils.o -c math_utils.c $(CFLAGS)

lpm_trie/lpm_trie.o: lpm_trie/lpm_trie.c lpm_trie/lib/double-chain.h
	gcc -o lpm_trie/lpm_trie.o -c lpm_trie/lpm_trie.c $(CFLAGS)

lpm_trie/lib/double-chain.o: lpm_trie/lib/double-chain.c lpm_trie/lib/double-chain-impl.h
	gcc -o lpm_trie/lib/double-chain.o -c lpm_trie/lib/double-chain.c $(CFLAGS)

lpm_trie/lib/double-chain-impl.o: lpm_trie/lib/double-chain-impl.c
	gcc -o lpm_trie/lib/double-chain-impl.o -c lpm_trie/lib/double-chain-impl.c $(CFLAGS)
	
nf_time.o: nf_time.c nf_time.h
	gcc -o nf_time.o -c nf_time.c $(CFLAGS)


# Include parent (in a convoluted way cause of DPDK)
include $(abspath $(dir $(lastword $(MAKEFILE_LIST))))/../Makefile



endif


#version like unverified-nat

include $(RTE_SDK)/mk/rte.vars.mk

# binary name
APP = router

# sources
SRCS-y := router.c parse_utils.c lpm_trie/lpm_trie.c lpm_trie/lib/double-chain.c lpm_trie/lib/double-chain-impl.c \
          ../nf_main.c \
          ../lib/nf_time.c 
    

# gcc flags
CFLAGS += -O3
CFLAGS += -I.. -I../..
CFLAGS += -std=gnu99

# disable warnings triggered by DPDK
CFLAGS += -Wno-implicit-function-declaration
CFLAGS += -Wno-nested-externs

include $(RTE_SDK)/mk/rte.extapp.mk
