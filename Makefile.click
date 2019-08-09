# Makefile for Click baseline NFs

CLICK_DIR := $(VIGOR_DIR)/fastclick

CLICK_BATCH_PARAM := --disable-batch
ifeq (true,$(VIGOR_USE_BATCH))
CLICK_BATCH_PARAM := --enable-auto-batch
endif

compile:
	@echo 'No explicit compilation step here, since we need to know whether batching is enabled to compile and that is done at run time'

# Cache batch state so we can run all click baselines and only do the make once, it takes quite a while
# Some of the configure params may be their defaults, but better safe than sorry
run:
	@if [ ! -e '$(CLICK_DIR)/.batch_state' ] || [ "$$(cat $(CLICK_DIR)/.batch_state)" != '$(CLICK_BATCH_PARAM)' ]; then \
	 printf '\n\n!!!\nConfiguring/making click, this is going to take a while...\n!!!\n\n'; \
	 cd $(CLICK_DIR); CFLAGS="-g -O3" CXXFLAGS="-g -std=gnu++11 -O3" ./configure --quiet --enable-multithread --disable-linuxmodule --enable-intel-cpu \
	                                                                             --enable-user-multithread --disable-dynamic-linking --enable-poll \
	                                                                             --enable-bound-port-transfer --enable-dpdk --with-netmap=no --enable-zerocopy \
	                                                                             --disable-dpdk-pool --disable-dpdk-packet $(CLICK_BATCH_PARAM); \
	                                                                 make; \
	 echo '$(CLICK_BATCH_PARAM)' > '$(CLICK_DIR)/.batch_state'; \
	fi
	@sudo $(CLICK_DIR)/bin/click --dpdk $(NF_DPDK_ARGS) -- nf.click
