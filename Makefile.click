# Makefile for Click baseline NFs

CLICK_DIR := $(VIGOR_DIR)/fastclick
CLICK_BATCH_SIZE := 1
ifeq (true,$(VIGOR_USE_BATCH))
CLICK_DIR := $(VIGOR_DIR)/fastclick-batch
CLICK_BATCH_SIZE := 32
endif

NF_PROCESS_NAME := click

compile:
	@echo 'No compile needed for Click NFs!'

run:
	@printf '\n\n!!!\nClick may incorrectly claim that the CPU\n'
	@printf 'cores are not on the same NUMA node as the NICs, ignore this.\n!!!\n\n'
	@sudo $(CLICK_DIR)/bin/click burst=$(CLICK_BATCH_SIZE) --dpdk $(NF_DPDK_ARGS) -- nf.click
