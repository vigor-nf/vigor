# pick one map of: ruby, DPDK, stdlib
NF_FILES := nat_main.c nat_config.c ruby/st.c nat_map_ruby.c \
#          nat_map_dpdk.c
#          nat_map_cppstl.c

# "Verification" arguments
NF_VERIF_ARGS := --lan-dev 0 \
                 --wan 1 \
                 --eth-dest 0,01:23:45:67:89:00 \
                 --eth-dest 1,01:23:45:67:89:01

# Include parent (in a convoluted way cause of DPDK)
include $(abspath $(dir $(lastword $(MAKEFILE_LIST))))/../Makefile

# C++ compiler
CC := g++
CFLAGS := $(filter-out -std=gnu99,$(CFLAGS))
CFLAGS += -std=gnu++11
LDFLAGS += -lstdc++
# Ruby needs that if it's, well, not Ruby
CFLAGS += -DNOT_RUBY
# Ruby's onigmo generates a ton of these
CFLAGS += -Wno-narrowing
