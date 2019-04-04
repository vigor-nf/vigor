#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stddef.h>
#include <stdbool.h>

#define TBL_PLEN_MAX 32
#define BYTE_SIZE 8

#define TBL_24_FLAG_MASK 0x8000
#define TBL_24_MAX_ENTRIES 16777216//= 2^24
#define TBL_24_VAL_MASK 0x7FFF
#define TBL_24_PLEN_MAX 24

#define TBL_LONG_OFFSET_MAX 256
#define TBL_LONG_FACTOR 256
#define TBL_LONG_MAX_ENTRIES 65536 //= 2^16

#define MAX_NEXT_HOP_VALUE 0x7FFF

/*
 * http://tiny-tera.stanford.edu/~nickm/papers/Infocom98_lookup.pdf
 * */

// I assume that the rules will be added from the lower prefixlen to the bigger prefixlen
// Each new rule will simply overwrite any existing rule where it should exist
/*	The entries in tbl_24 are as follows:
 * 		bit15: 0->next hop, 1->tbl_long lookup
 * 		bit14-0: value of next hop or index in tbl_long
 */
/*	The entries in tbl_long are as follows:
 * 	bit15-0: value of next hop
 */
//max next hop value is 2^15 - 1.


struct tbl{
    uint16_t*tbl_24;
    uint16_t* tbl_long;
    uint8_t tbl_long_index;
};

struct key{
    uint32_t data;
    uint8_t prefixlen;
    uint16_t route;
};

/*@
predicate table(struct tbl* t, uint16_t* tbl_24, uint16_t* tbl_long, int long_index; list<uint16_t> t_24, list<uint16_t> t_l) = 
	malloc_block_tbl(t) &*& malloc_block_ushorts(tbl_24, TBL_24_MAX_ENTRIES) &*& malloc_block_ushorts(tbl_long, TBL_LONG_MAX_ENTRIES)
	&*& t->tbl_24 |-> tbl_24 &*& t->tbl_long |-> tbl_long &*& t->tbl_long_index |-> long_index
	&*& tbl_24[0..TBL_24_MAX_ENTRIES] |-> t_24 &*& tbl_long[0..TBL_LONG_MAX_ENTRIES] |-> t_l
	&*& long_index >= 0 &*& long_index <= TBL_LONG_FACTOR;

predicate key(struct key* k) = 
	malloc_block_key(k) &*& k->data |-> ?ipv4 &*& k->prefixlen |-> ?prefixlen &*& k->route |-> ?route;
@*/

//In header only for tests
uint32_t tbl_24_extract_first_index(uint32_t data);
uint16_t tbl_long_extract_first_index(uint32_t data, uint16_t base_index);
uint16_t tbl_24_entry_set_flag(uint16_t entry);
uint32_t build_mask_from_prefixlen(uint8_t prefixlen);
void fill_with_zeros(uint16_t *array, uint32_t size);
uint32_t compute_rule_size(uint8_t prefixlen);

struct tbl *tbl_allocate();

void tbl_free(struct tbl *tbl);

int tbl_update_elem(struct tbl *_tbl, struct key *_key);

int tbl_lookup_elem(struct tbl *_tbl, uint32_t data);
