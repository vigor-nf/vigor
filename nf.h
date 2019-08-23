#pragma once

#include <stdint.h>

#include "libvig/verified/vigor_time.h"

#define FLOOD_FRAME ((uint16_t) -1)

struct rte_mbuf;
struct nf_config;

void nf_init(void);
int nf_process(struct rte_mbuf *pkt, vigor_time_t now);

extern struct nf_config config;
void nf_config_init(int argc, char **argv);
void nf_config_usage(void);
void nf_config_print(void);

#ifdef KLEE_VERIFICATION
void nf_loop_iteration_border(unsigned lcore_id, vigor_time_t time);
#endif
