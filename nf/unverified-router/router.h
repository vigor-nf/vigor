
#ifndef _router_h
#define _router_h

#define MAX_ROUTES_ENTRIES 256

#include "lpm_trie/lpm_trie_mem.h"
#include "parse_utils.h"
#include <stdio.h>
//#include <math.h>
#include <ctype.h>
#include <linux/limits.h>
#include <sys/types.h>
#include <unistd.h>
#include <rte_common.h>
#include <rte_ethdev.h>
#include <rte_mbuf.h>
#include <cmdline_parse_etheraddr.h>
#include "nf_time.h"


/**
 * insert all routes from the csv file to the lpm trie
 */
void insert_all(FILE * f);


/**
 * Routes packets using a LPM Trie
 */
uint16_t nf_core_process(struct rte_mbuf* mbuf, vigor_time_t now);


/**
 * Initialize the NF
 */
void nf_core_init(void);

#endif
