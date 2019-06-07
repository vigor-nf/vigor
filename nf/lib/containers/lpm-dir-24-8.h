#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stddef.h>
#include <stdbool.h>

//@ #include "lpm-dir-24-8.gh"

#define lpm_PLEN_MAX 32
#define BYTE_SIZE 8

#define INVALID 0xFFFF

#define lpm_24_FLAG_MASK 0x8000 // == 0b1000 0000 0000 0000
#define lpm_24_MAX_ENTRIES 16777216//= 2^24
#define lpm_24_VAL_MASK 0x7FFF
#define lpm_24_PLEN_MAX 24

#define lpm_LONG_OFFSET_MAX 256
#define lpm_LONG_FACTOR 256
#define lpm_LONG_MAX_ENTRIES 65536 //= 2^16

#define MAX_NEXT_HOP_VALUE 0x7FFF

/*
 * http://tiny-tera.stanford.edu/~nickm/papers/Infocom98_lookup.pdf
 * */

// I assume that the rules will be in ascending order of prefixlen
// Each new rule will simply overwrite any existing rule where it should exist
/*	The entries in lpm_24 are as follows:
 * 		bit15: 0->next hop, 1->lpm_long lookup
 * 		bit14-0: value of next hop or index in lpm_long
 */
/*	The entries in lpm_long are as follows:
 * 	bit15-0: value of next hop
 */
//max next hop value is 2^15 - 1.


struct lpm;

struct rule {
  uint32_t ipv4;
  uint8_t prefixlen;
  uint16_t route;
};

/*@
  predicate table(struct lpm* t, dir_24_8 dir);
  predicate rule(struct rule* r; uint32_t ipv4, uint8_t prefixlen,
                uint16_t route); @*/



struct lpm *lpm_allocate();
//@ requires true;
/*@ ensures result == 0 ? 
              true 
            : 
              table(result, dir_init()); @*/

void lpm_free(struct lpm *_lpm);
//@ requires table(_lpm, _);
//@ ensures true;

int lpm_update_elem(struct lpm *_lpm, struct rule *_rule);
//@ requires table(_lpm, ?dir) &*& rule(_rule, ?ipv4, ?plen, ?route);
/*@ ensures table(_lpm,
                  add_rule(dir,
                           init_rule(ipv4, plen, route)
                  )
            )
            &*& rule(_rule, ipv4, plen, route); @*/

int lpm_lookup_elem(struct lpm *_lpm, uint32_t ipv4);
//@ requires table(_lpm, ?dir);
/*@ ensures table(_lpm, dir) &*&
            result == lpm_dir_24_8_lookup(Z_of_int(ipv4, N32),dir); @*/
