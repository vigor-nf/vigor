# Binary name
APP := verified_router

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
#include $(abspath $(dir $(lastword $(MAKEFILE_LIST))))/../Makefile

#dyn_value.h.gen.c dyn_value.h.gen.h: dyn_value.h
#	bash ../../codegen/generate.sh dyn_value.h

#stat_key.h.gen.c stat_key.h.gen.h ../lib/stubs/ether_addr.h.gen.c ../lib/stubs/ether_addr.h.gen.h: stat_key.h ../lib/stubs/ether_addr.h
#	bash ../../codegen/generate.sh stat_key.h

#bridge_loop.h bridge_loop.c bridge_state.h bridge_state.c: bridge_data_spec.ml
#bash ../../codegen/gen-loop-boilerplate.sh bridge_data_spec.ml
