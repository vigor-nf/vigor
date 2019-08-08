# pick one map of: ruby, DPDK, stdlib
NF_FILES := nat_main.c nat_config.c ruby/st.c nat_map_ruby.c \
#          nat_map_dpdk.c
#          nat_map_cppstl.c

NF_ARGS := --lan-dev 0 \
           --wan 1 \
           --expire $(or $(EXPIRATION_TIME),10) \
           --starting-port 0 \
           --max-flows 65536 \
           --extip $(or $(MB_IP_EXTERNAL),0.0.0.0) \
           --eth-dest 0,$(or $(TESTER_MAC_EXTERNAL),01:23:45:67:89:00) \
           --eth-dest 1,$(or $(TESTER_MAC_INTERNAL),01:23:45:67:89:01)

NF_LAYER := 4

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
