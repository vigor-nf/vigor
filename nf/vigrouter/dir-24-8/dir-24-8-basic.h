#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stddef.h>

#define TBL_PLEN_MAX 32

#define TBL_24_FLAG_MASK 1 << 15
#define TBL_24_PLEN_MASK 0x7F00
#define TBL_24_MAX_ENTRIES 16777216//= 2^24
#define TBL_24_VAL_MASK 0x00FF
#define TBL_24_PLEN_MAX 24

#define TBL_LONG_OFFSET_MAX 256
#define TBL_LONG_FACTOR 256
#define TBL_LONG_MAX_ENTRIES 65536 //= 2^16
#define TBL_LONG_PLEN_MASK 0xFF00
#define TBL_LONG_VAL_MASK 0x00FF

/*
 * http://tiny-tera.stanford.edu/~nickm/papers/Infocom98_lookup.pdf
 * */

struct entry{
	struct rule *current_rule;
};

struct rule{
	uint8_t prefixlen;
	uint16_t value;
	struct rule *next;
};

struct tbl{
    struct entry **tbl_24;
    struct entry **tbl_long;
    size_t tbl_long_index;
    size_t n_entries;
    size_t max_entries;
};

struct key{
    uint8_t data[4];
    uint8_t prefixlen;
};

/*@
predicate table(struct tbl* t; list<uint16_t> tbl_24, list<uint16_t> tbl_long) = 
	malloc_block_tbl(t)
	&*& t->tbl_24 |-> ?t_24 &*& t->tbl_long |-> ?t_l &*& t->max_entries |-> ?max_entries &*& t->n_entries |-> ?n_entries
	&*& t_24 != 0 &*& t_l != 0 &*& n_entries >= 0 &*& max_entries > 0
	&*& t_24[0..TBL_24_MAX_ENTRIES] |-> tbl_24
	&*& t_l[0..TBL_LONG_MAX_ENTRIES] |-> tbl_long;

predicate key(struct key* k; list<uint8_t> ipv4) = 
	malloc_block_key(k) &*& k->data |-> ?data &*& k->prefixlen |-> ?prefixlen &*& malloc_block_pointers(data, 4) &*& data[0..4] |-> ipv4;
@*/

//In header only for tests
size_t tbl_24_extract_first_index(uint8_t *data);
size_t tbl_24_extract_last_index(struct key *key);
uint16_t tbl_24_entry_set_flag(uint16_t entry);
size_t correct_first_index_with_mask(size_t first_index, uint8_t prefixlen);
size_t build_mask_from_prefixlen(uint8_t prefixlen);
void fill_with_zeros(struct entry** array, size_t size);
void linked_list_insertion(struct entry* _entry, uint8_t prefixlen, uint16_t value);
void linked_list_deletion(struct entry* _entry, uint8_t prefixlen);
void free_entries(struct entry **entries, size_t size);
void free_rules(struct rule* head);


struct tbl *tbl_allocate(size_t max_entries);

void tbl_free(struct tbl *tbl);

int tbl_update_elem(struct tbl *_tbl, struct key *_key, uint8_t value);

int tbl_delete_elem(struct tbl *_tbl, struct key *_key);

int tbl_lookup_elem(struct tbl *_tbl, uint8_t* data);

