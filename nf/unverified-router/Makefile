

include $(RTE_SDK)/mk/rte.vars.mk

#select the lookup algorithm (TRIE, DIR)
ALGO = TRIE

#select test mode or normal mode
MODE = TEST

# binary name
APP = router

ifneq (TEST, $(MODE))

# sources  normal mode
SRCS-y := router.c parse_utils.c \
          ../nf_main.c \
          ../lib/nf_time.c \
          ../lib/containers/double-chain-impl.c \
          ../lib/containers/double-chain.c \
          ../lib/containers/lpm_trie.c \

else

# sources  test mode
SRCS-y := router.c parse_utils.c \
          tests.c \
          ../lib/nf_time.c \
          ../lib/containers/double-chain-impl.c \
          ../lib/containers/double-chain.c \
          ../lib/containers/lpm_trie.c \

CFLAGS += -DTEST_M

endif

# gcc flags
CFLAGS += -O3
CFLAGS += -I.. -I../..
CFLAGS += -std=c99
CFLAGS += -D_POSIX_C_SOURCE=199309L

# disable warnings triggered by DPDK
CFLAGS += -Wno-implicit-function-declaration
CFLAGS += -Wno-nested-externs
CFLAGS += -D$(ALGO)

include $(RTE_SDK)/mk/rte.extapp.mk


