

include $(RTE_SDK)/mk/rte.vars.mk


#use ip CACHE terrible performances with changing ip. Pretty much the same with constant ip... not really usefull 
USE = NO_CACHE

# binary name
APP = router


# sources  normal mode
SRCS-y := router.c router_config.c parse_utils.c \
          nf_main.c \
          ../lib/nf_util.c \
          ../lib/packet-io.c \
          ../lib/nf_time.c \
          ../lib/containers/double-chain-impl.c \
          ../lib/containers/double-chain.c \
          ../lib/containers/lpm_trie.c \



# gcc flags
CFLAGS += -O3
CFLAGS += -I.. -I../..
CFLAGS += -std=c99
CFLAGS += -D_POSIX_C_SOURCE=199309L
CFLAGS += -g 

# disable warnings triggered by DPDK
CFLAGS += -Wno-implicit-function-declaration
CFLAGS += -Wno-nested-externs
CFLAGS += -D$(USE)


include $(RTE_SDK)/mk/rte.extapp.mk


