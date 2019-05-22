#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stddef.h>
#include <stdbool.h>

//@ #include "dir-24-8-basic.gh"

#define TBL_PLEN_MAX 32
#define BYTE_SIZE 8

#define INVALID 0xFFFF

#define TBL_24_FLAG_MASK 0x8000 // == 0b1000 0000 0000 0000
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

// I assume that the rules will be in ascending order of prefixlen
// Each new rule will simply overwrite any existing rule where it should exist
/*	The entries in tbl_24 are as follows:
 * 		bit15: 0->next hop, 1->tbl_long lookup
 * 		bit14-0: value of next hop or index in tbl_long
 */
/*	The entries in tbl_long are as follows:
 * 	bit15-0: value of next hop
 */
//max next hop value is 2^15 - 1.


struct tbl;

struct key{
  uint32_t data;
  uint8_t prefixlen;
  uint16_t route;
};

/*@
  predicate table(struct tbl* t, dir_24_8 dir);
  predicate key(struct key* k; uint32_t ipv4, uint8_t prefixlen,
                uint16_t route);
@*/



struct tbl *tbl_allocate();
//@ requires true;
/*@ ensures result == 0 ? 
      true 
    : 
      table(result, dir_init());

@*/

void tbl_free(struct tbl *_tbl);
//@ requires table(_tbl, _);
//@ ensures true;

int tbl_update_elem(struct tbl *_tbl, struct key *_key);
//@ requires table(_tbl, ?dir) &*& key(_key, ?ipv4, ?plen, ?route);
/*@ ensures table(_tbl,
                  add_rule(dir,
                           init_rule(ipv4, plen, route)
                  )
            )
            &*& key(_key, ipv4, plen, route);
@*/

/*int tbl_lookup_elem(struct tbl *_tbl, uint32_t data);
//@ requires table(_tbl, ?dir);
/* @ ensures table(_tbl, dir) &*&
            result == lpm_dir_24_8_lookup(Z_of_int(data, N32),dir);
@*/
