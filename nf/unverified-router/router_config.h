#pragma once

#include <stdint.h>

// TODO can't really include rte_max_ethports here but need it :/

#define CONFIG_FNAME_LEN 512

struct router_config {
  // Expiration time of flows in seconds
  uint64_t expiration_time;

  // Size of the dynamic filtering table
  uint32_t dyn_capacity;

  // The static configuration file name
  char static_config_fname[CONFIG_FNAME_LEN];
};


void router_config_init(struct router_config* config, int argc, char** argv);

void router_config_cmdline_print_usage(void);

void router_print_config(struct router_config* config);
