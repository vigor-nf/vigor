# C++ compiler
CC = g++
CFLAGS += -std=gnu++11
# Ruby needs that if it's, well, not Ruby
CFLAGS += -DNOT_RUBY
# Ruby's onigmo generates a ton of these
CFLAGS += -Wno-narrowing

LDFLAGS += -lstdc++

# pick one map of: ruby, DPDK, stdlib
NF_FILES := nat_main.c nat_config.c ruby/st.c nat_map_ruby.c \
          ../nf_main.c \
          ../lib/nf_time.c \
          ../lib/nf_util.c \
          ../lib/packet-io.c
#          nat_map_dpdk.c
#          nat_map_cppstl.c

# Include parent (in a convoluted way cause of DPDK)
include $(RTE_SDK)/mk/rte.extapp.mk
