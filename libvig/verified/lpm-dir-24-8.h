#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stddef.h>
#include <stdbool.h>

//@ #include "../proof/lpm-dir-24-8.gh"

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

// http://tiny-tera.stanford.edu/~nickm/papers/Infocom98_lookup.pdf

// I assume that the rules will be in ascending order of prefixlen
// Each new rule will simply overwrite any existing rule where it should exist
// The entries in lpm_24 are as follows:
//   bit15: 0->next hop, 1->lpm_long lookup
//   bit14-0: value of next hop or index in lpm_long
//
// The entries in lpm_long are as follows:
//   bit15-0: value of next hop
//
//max next hop value is 2^15 - 1.


struct lpm;

/*@ predicate table(struct lpm* t, dir_24_8 dir); @*/



int lpm_allocate(struct lpm **lpm_out);
//@ requires *lpm_out |-> ?old_lo;
/*@ ensures result == 0 ?
              *lpm_out |-> old_lo :
              *lpm_out |-> ?new_lo &*&
              table(new_lo, dir_init()) &*&
              result == 1; @*/

void lpm_free(struct lpm *_lpm);
//@ requires table(_lpm, _);
//@ ensures true;

int lpm_update_elem(struct lpm *_lpm, uint32_t prefix,
                    uint8_t prefixlen, uint16_t value);
/*@ requires table(_lpm, ?dir) &*&
             prefixlen >= 0 &*& prefixlen <= 32 &*&
             value != INVALID &*&
             0 <= value &*& value <= MAX_NEXT_HOP_VALUE &*&
             false == extract_flag(value) &*&
             true == valid_entry24(value) &*&
             true == valid_entry_long(value); @*/
/*@ ensures can_insert(dir, prefix, prefixlen) == (result != 0) &*&
            result != 0 ?
              table(_lpm, add_rule(dir, init_rule(prefix, prefixlen, value)))
            :
              table(_lpm, dir); @*/

int lpm_lookup_elem(struct lpm *_lpm, uint32_t prefix);
//@ requires table(_lpm, ?dir);
/*@ ensures table(_lpm, dir) &*&
            result == lpm_dir_24_8_lookup(Z_of_int(prefix, N32),dir); @*/
