
#ifndef __ROUTER_H_INCLUDED__
#define __ROUTER_H_INCLUDED__

#define MAX_ROUTES_ENTRIES 1200000
#define MAX_TBL_8 80000 // number of 8bits tables for the dir-24-8 algorithm
#define CACHE_SIZE 32

#include "libvig/nf_time.h"
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
#include "nf.h"
#include "libvig/nf_util.h"

// the DIR-24-8 that will be used by the nf (global variable)
extern struct rte_lpm *lpm_dir;

/**
 * insert all routes from the csv file to the lpm trie
 */
void insert_all(FILE *f);
#endif
