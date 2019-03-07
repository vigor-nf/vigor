#include "parse_utils.h"
#include "lpm/lpm_trie/lpm_trie_mem.h"
#include <stdio.h>

struct lpm_trie_key *lpm_trie_key_alloc(size_t prefixlen, uint8_t *data);
int *insert_all(FILE * f, struct lpm_trie * t);
void nf_core_init(void);

