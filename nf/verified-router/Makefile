# Binary name
APP := verified_router

#compilation flags
CFLAGS=-W -Wall -std=c11 -pedantic


all: tests 

#router: router.o parse_utils.o math_utils.o lpm_trie/lpm_trie.o lpm_trie/lib/double-chain-impl.o lpm_trie/lib/double-chain.o
	#gcc -o router_main router_main.o parse_utils.o math_utils.o lpm_trie/lpm_trie.o lpm_trie/lib/double-chain-impl.o lpm_trie/lib/double-chain.o
	
tests: tests.o parse_utils.o router_main.o lpm/lpm_trie/lpm_trie.o lpm/lpm_trie/lib/double-chain-impl.o lpm/lpm_trie/lib/double-chain.o
	gcc -o tests tests.o parse_utils.o router_main.o lpm/lpm_trie/lpm_trie.o lpm/lpm_trie/lib/double-chain-impl.o lpm/lpm_trie/lib/double-chain.o
	
tests.o: tests.c parse_utils.h router_main.h
	gcc -o tests.o -c tests.c $(CFLAGS)

router_main.o: router_main.c lpm/lpm_trie/lpm_trie_mem.h parse_utils.h router_main.h
	gcc -o router_main.o -c router_main.c $(CFLAGS)

parse_utils.o: parse_utils.c parse_utils.h
	gcc -o parse_utils.o -c parse_utils.c $(CFLAGS)

lpm/lpm_trie/lpm_trie.o: lpm/lpm_trie/lpm_trie.c lpm/lpm_trie/lib/double-chain.h
	gcc -o lpm/lpm_trie/lpm_trie.o -c lpm/lpm_trie/lpm_trie.c $(CFLAGS)

lpm/lpm_trie/lib/double-chain.o: lpm/lpm_trie/lib/double-chain.c lpm/lpm_trie/lib/double-chain-impl.h
	gcc -o lpm/lpm_trie/lib/double-chain.o -c lpm/lpm_trie/lib/double-chain.c $(CFLAGS)

lpm/lpm_trie/lib/double-chain-impl.o: lpm/lpm_trie/lib/double-chain-impl.c
	gcc -o lpm/lpm_trie/lib/double-chain-impl.o -c lpm/lpm_trie/lib/double-chain-impl.c $(CFLAGS)


# Include parent (in a convoluted way cause of DPDK)
include $(abspath $(dir $(lastword $(MAKEFILE_LIST))))/../Makefile