#ifndef __ROUTER_H_INCLUDED__
#define __ROUTER_H_INCLUDED__

#define MAX_ROUTES_ENTRIES 120000
#define MAX_TBL_8  80000	//number of 8bits tables for the dir-24-8 algorithm
#define CACHE_SIZE 32

#include "lib/nf_time.h"
#include "lib/containers/lpm-dir-24-8.h"
#include <rte_lpm.h>
#include "parse_utils.h"
#include <stdio.h>
#include <ctype.h>
#include <linux/limits.h>
#include <sys/types.h>
#include <unistd.h>
#include <rte_common.h>
#include <rte_ethdev.h>
#include <rte_mbuf.h>
#include <rte_ip.h>
#include <cmdline_parse_etheraddr.h>
#include "lib/nf_forward.h"
#include "lib/nf_util.h"

//the DIR-24-8 that will be used by the nf (global variable)
extern struct lpm * lpm_table;			

/**
 * insert all routes from the csv file to the lpm trie
 */
void insert_all(FILE * f);

/**
 * Routes packets using a LPM Trie
 */
int nf_core_process(struct rte_mbuf* mbuf, vigor_time_t now);

/**
 * Initialize the NF
 */
void nf_core_init(void);

#endif//__ROUTER_H_INCLUDED__
