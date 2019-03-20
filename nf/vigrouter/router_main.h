#include "parse_utils.h"
#include "lib/containers/lpm_trie_mem.h"
#include <stdio.h>
#include <linux/limits.h>
#include <sys/types.h>
#include <unistd.h>
#include <rte_common.h>
#include <rte_ethdev.h>
#include <rte_mbuf.h>
#include <cmdline_parse_etheraddr.h>
#include "lib/nf_forward.h"
//#include "lib/nf_util.h"
//#include "lib/nf_log.h"

//#include "lib/containers/double-chain.h"


struct lpm_trie_key *lpm_trie_key_alloc(size_t prefixlen, uint8_t *data);
void insert_all(FILE * f, struct lpm_trie *routing_table);
void nf_core_init(void);
int nf_core_process(struct rte_mbuf* mbuf, vigor_time_t now);

