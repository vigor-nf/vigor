# Binary name
APP := router

#compilation flags
CFLAGS=-W -Wall -std=c11 -pedantic

# Runtime and verification files
#NF_FILES := bridge_main.c bridge_config.c stat_key.h.gen.c dyn_value.h.gen.c ../lib/stubs/ether_addr.h.gen.c bridge_state.c

# Verification files
#NF_VERIF_FILES := bridge_loop.c

# Verification arguments
#NF_VERIF_ARGS := --expire 10 --capacity 100 --config no-file.cfg

#AUTO_GEN_FILES := dyn_value.h.gen.c dyn_value.h.gen.h \
 #                 stat_key.h.gen.c stat_key.h.gen.h \
  #                ../lib/stubs/ether_addr.h.gen.c ../lib/stubs/ether_addr.h.gen.h \
   #               bridge_loop.c bridge_loop.h \
    #              bridge_state.c bridge_state.h

#all: $(AUTO_GEN_FILES) $(APP)

all: tests 

#router: router.o parse_utils.o math_utils.o lpm_trie/lpm_trie.o lpm_trie/lib/double-chain-impl.o lpm_trie/lib/double-chain.o
#	gcc -o router router.o parse_utils.o math_utils.o lpm_trie/lpm_trie.o lpm_trie/lib/double-chain-impl.o lpm_trie/lib/double-chain.o
	
tests: tests.o parse_utils.o math_utils.o router.o lpm_trie/lpm_trie.o lpm_trie/lib/double-chain-impl.o lpm_trie/lib/double-chain.o
	gcc -o tests tests.o parse_utils.o math_utils.o router.o lpm_trie/lpm_trie.o lpm_trie/lib/double-chain-impl.o lpm_trie/lib/double-chain.o
	
tests.o: tests.c parse_utils.h math_utils.h router.h
	gcc -o tests.o -c tests.c $(CFLAGS)

router.o: router.c lpm_trie/lpm_trie_mem.h parse_utils.h router.h
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


# Include parent (in a convoluted way cause of DPDK)
#include $(abspath $(dir $(lastword $(MAKEFILE_LIST))))/../Makefile

#dyn_value.h.gen.c dyn_value.h.gen.h: dyn_value.h
#	bash ../../codegen/generate.sh dyn_value.h

#stat_key.h.gen.c stat_key.h.gen.h ../lib/stubs/ether_addr.h.gen.c ../lib/stubs/ether_addr.h.gen.h: stat_key.h ../lib/stubs/ether_addr.h
#	bash ../../codegen/generate.sh stat_key.h

#bridge_loop.h bridge_loop.c bridge_state.h bridge_state.c: bridge_data_spec.ml
#bash ../../codegen/gen-loop-boilerplate.sh bridge_data_spec.ml
