#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stddef.h>

#define TBL_PLEN_MAX 32

#define TBL_24_FLAG_MASK 1 << 15
#define TBL_24_PLEN_MASK 0x7F00
#define TBL_24_MAX_ENTRIES 2 << 24
#define TBL_24_VAL_MASK 0x00FF
#define TBL_24_PLEN_MAX 24

#define TBL_LONG_OFFSET_MAX 256
#define TBL_LONG_FACTOR 256
#define TBL_LONG_MAX_ENTRIES 2 << 16
#define TBL_LONG_PLEN_MASK 0xFF00
#define TBL_LONG_VAL_MASK 0x00FF



struct tbl{
    uint16_t *tbl_24;
    uint16_t *tbl_long;
    size_t tbl_long_index;
    size_t n_entries;
    size_t max_entries;
};

struct key{
    uint8_t data[4];
    uint8_t prefixlen;
};

//In header only for tests
size_t tbl_24_extract_first_index(uint8_t *data);
size_t tbl_24_extract_last_index(struct key *key);
uint16_t tbl_24_entry_put_plen(uint16_t entry, uint8_t prefixlen);
uint16_t tbl_long_entry_put_plen(uint16_t entry, uint8_t prefixlen);
uint16_t tbl_24_entry_set_flag(uint16_t entry);

struct tbl *tbl_allocate(size_t max_entries);

void tbl_free(struct tbl *tbl);

int tbl_update_elem(struct tbl *_tbl, struct key *_key, uint8_t value);

int tbl_delete_elem(struct tbl *_tbl, struct key *_key);

int tbl_lookup_elem(struct tbl *_tbl, struct key *_key);
