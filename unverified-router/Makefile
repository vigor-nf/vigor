

include $(RTE_SDK)/mk/rte.vars.mk



# binary name
APP = router


# sources  normal mode
SRCS-y := router.c parse_utils.c \
          ../nf_main.c \
          ../libvig/nf_util.c \
          ../libvig/packet-io.c \
          ../libvig/nf_time.c \
          ../libvig/containers/double-chain-impl.c \
          ../libvig/containers/double-chain.c \



# gcc flags
CFLAGS += -O3
CFLAGS += -I.. -I../..
CFLAGS += -std=c99
CFLAGS += -D_POSIX_C_SOURCE=199309L
CFLAGS += -g 

# disable warnings triggered by DPDK
CFLAGS += -Wno-implicit-function-declaration
CFLAGS += -Wno-nested-externs



include $(RTE_SDK)/mk/rte.extapp.mk

