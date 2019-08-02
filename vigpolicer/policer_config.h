#pragma once

#include <stdint.h>

#define CONFIG_FNAME_LEN 512

struct policer_config {
  // LAN (i.e. internal) device
  uint16_t lan_device;

  // WAN device, i.e. external
  uint16_t wan_device;

// Policer rate in B/s
  uint32_t rate;

  // Policer burst size in B
  uint32_t burst;

  // Size of the dynamic filtering table
  uint32_t dyn_capacity;
};


void policer_config_init(struct policer_config* config,
                        int argc, char** argv);

void policer_config_cmdline_print_usage(void);

void policer_print_config(struct policer_config* config);
