#pragma once

#include <stdint.h>
#include "libvig/verified/vigor-time.h"

#define CONFIG_FNAME_LEN 512

struct nf_config {
  // Expiration time of flows, in microseconds
  uint32_t expiration_time;

  // Size of the dynamic filtering table
  uint32_t dyn_capacity;

  // The static configuration file name
  char static_config_fname[CONFIG_FNAME_LEN];
};
