
#ifndef _router_h
#define _router_h

#define MAX_ROUTES_ENTRIES 256
#define MAX_TBL_8 	64	//number of 8bits tables for the dir-24-8 algorithm


#include "lib/nf_time.h"
#include "lib/containers/lpm_trie_mem.h"
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
#include "router_config.h"
#include "lib/nf_forward.h"
#include "lib/nf_util.h"



#ifdef TRIE

//the Trie that will be used by the nf (global variable)
extern struct lpm_trie * lpm_trie;	

#else

//the DIR-24-8 that will be used by the nf (global variable)
extern struct rte_lpm * lpm_dir;			

#endif



/**
 * Helper function to initialize the key for a trie
 */
struct lpm_trie_key * lpm_trie_key_alloc(size_t prefixlen, uint8_t *data);



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

#endif
