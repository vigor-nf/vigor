

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

# disable warnings triggered by DPDK
CFLAGS += -Wno-implicit-function-declaration
CFLAGS += -Wno-nested-externs

include $(RTE_SDK)/mk/rte.extapp.mk


