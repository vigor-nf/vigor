#pragma once

#include <stdint.h>
#include <stdlib.h>

// TODO can't really include rte_max_ethports here but need it :/



struct router_config {
  
 
};


void router_config_init(struct router_config* config, int argc, char** argv);

void router_config_cmdline_print_usage(void);

void router_print_config(struct router_config* config);
