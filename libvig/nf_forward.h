#pragma once

#include <inttypes.h>

#include "libvig/packet-io.h"
#include "libvig/nf_time.h"


struct rte_mbuf;

void nf_core_init(void);

static const uint16_t FLOOD_FRAME = -1;
int nf_core_process(struct rte_mbuf* pkt, vigor_time_t now);

void nf_config_init(int argc, char** argv);
void nf_config_set(void* value);
void nf_config_cmdline_print_usage(void);
void nf_print_config(void);

#ifdef KLEE_VERIFICATION
void nf_loop_iteration_border(unsigned lcore_id,
                              vigor_time_t time);
#endif //KLEE_VERIFICATION
