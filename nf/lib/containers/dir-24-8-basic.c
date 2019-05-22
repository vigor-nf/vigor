#include "dir-24-8-basic.h"
//@ #include <nat.gh>
//@ #include <bitops.gh>


/*@
  predicate table(struct tbl* t, dir_24_8 dir) = 
    malloc_block_tbl(t) &*&
    t->tbl_24 |-> ?tbl_24 &*& t->tbl_long |-> ?tbl_long &*&
    t->tbl_long_index |-> ?long_index &*&
    malloc_block_ushorts(tbl_24, TBL_24_MAX_ENTRIES) &*&
    malloc_block_ushorts(tbl_long, TBL_LONG_MAX_ENTRIES) &*&
    tbl_24[0..TBL_24_MAX_ENTRIES] |-> ?tt_24 &*&
    tbl_long[0..TBL_LONG_MAX_ENTRIES] |-> ?tt_l &*&
    true == forall(tt_24, valid_entry24) &*&
    true == forall(tt_l, valid_entry_long) &*&
    build_tables(tt_24, tt_l, long_index) == dir &*&
    map(entry_24_mapping, tt_24) == dir_tbl24(dir) &*&
    map(entry_long_mapping, tt_l) == dir_tbl_long(dir) &*&
    length(tt_24) == length(dir_tbl24(dir)) &*&
    length(tt_l) == length(dir_tbl_long(dir)) &*&
    long_index >= 0 &*& long_index <= TBL_LONG_FACTOR;
  @*/

/*@
  predicate key(struct key* k; uint32_t ipv4, uint8_t prefixlen, uint16_t route)= 
    malloc_block_key(k) &*&
    k->data |-> ipv4 &*&
    k->prefixlen |-> prefixlen &*&
    k->route |-> route &*&
    prefixlen >= 0 &*& prefixlen <= 32 &*&
    route != INVALID &*& 0 <= route &*& route <= MAX_NEXT_HOP_VALUE &*&
    false == extract_flag(route) &*&
    true == valid_entry24(route) &*& true == valid_entry_long(route);
  @*/
  
/*@
  fixpoint bool boundaries(uint16_t elem){
    return 0 <= elem && elem <= 0xFFFF;
  }
@*/

/*@
  fixpoint bool is_none<t>(option<t> mapped){
    return mapped == none;
  }
@*/

/*@
  fixpoint bool check_INVALID(uint16_t current){
    return current == INVALID;
  }
  @*/

/*@
  lemma void flag_mask_MBS_one()
    requires TBL_24_FLAG_MASK == 0x8000;
    ensures extract_flag(TBL_24_FLAG_MASK) == true;
  {
    Z maskZ = Z_of_uintN(TBL_24_FLAG_MASK, N16);
    shiftright_def(TBL_24_FLAG_MASK, maskZ, nat_of_int(15));
    Z shifted = Z_shiftright(maskZ, nat_of_int(15));
    assert 1 == int_of_Z(shifted);
  }
  @*/

/*@
  lemma void flag_mask_or_x_begins_with_one(uint16_t x)
    requires 0 <= x &*& x <= 0xFFFF;
    ensures extract_flag(x | TBL_24_FLAG_MASK) == true;
  {

    Z xZ = Z_of_uintN(x, N16);
    Z maskZ = Z_of_uintN(TBL_24_FLAG_MASK, N16);
    flag_mask_MBS_one();
    assert true == extract_flag(TBL_24_FLAG_MASK);
  
    Z res = Z_or(xZ, maskZ);
    bitor_def(x, xZ, TBL_24_FLAG_MASK, maskZ);
    assert int_of_Z(res) == (x | TBL_24_FLAG_MASK);
  
    shiftright_def(int_of_Z(res), res, nat_of_int(15));
    Z shifted = Z_shiftright(res, nat_of_int(15));
    assert 1 == int_of_Z(shifted);
  }
  @*/

/*@
  lemma void flag_mask_or_x_not_affect_15LSB(uint16_t x)
    requires 0 <= x &*& x <= 0x7FFF;
    ensures x == ((x | TBL_24_FLAG_MASK) & TBL_24_VAL_MASK);
  {
    Z xZ = Z_of_uintN(x, N16);
    Z flagMask = Z_of_uintN(TBL_24_FLAG_MASK, N16);
    Z valueMask = Z_of_uintN(TBL_24_VAL_MASK, N16);
  
    bitor_def(x, xZ, TBL_24_FLAG_MASK, flagMask);
    Z orRes = Z_or(xZ, flagMask);
  
    bitand_def((x | TBL_24_FLAG_MASK), orRes, TBL_24_VAL_MASK, valueMask);
    Z andRes = Z_and(orRes, valueMask);
  
    assert andRes == xZ;
    assert int_of_Z(andRes) == int_of_Z(xZ);
  }
  @*/

/*@
  lemma void extract_value_is_value(uint16_t entry)
    requires 0 <= entry &*& entry <= 0x7FFF;
    ensures entry == extract_value(entry);
  {
    Z entryZ = Z_of_uintN(entry, N16);
    Z valuemask = Z_of_uintN(TBL_24_VAL_MASK, N16);
    
    bitand_def(entry, entryZ, TBL_24_VAL_MASK, valuemask);
    Z andRes = Z_and(entryZ, valuemask);
    
    assert andRes == entryZ;
  }
  @*/
  
/*@
  lemma void repeat_n_forall<t>(list<t> lst, nat size, t e, fixpoint(t, bool) p)
    requires lst == repeat_n(size, e) &*& true == p(e);
    ensures true == forall(lst, p); 
  {
    switch(lst){
      case nil:
      case cons(x, xs): 
        switch(size){
          case zero:
          case succ(n): repeat_n_forall(xs, n, e, p);
        }
    }
  }
  @*/

/*@
  lemma void repeat_n_append<t>(list<t> lst, t e, int size);
    requires lst == repeat_n(nat_of_int(size), e);
    ensures append(lst, cons(e, nil)) == repeat_n(nat_of_int(size+1), e);
  @*/

/*@
  lemma void new_invalid(uint16_t *t, uint32_t i, uint32_t size);
    requires t[0..i] |-> ?l1 &*&
             l1 == repeat_n(nat_of_int(i), INVALID) &*&
             t[i..size] |-> _;
    ensures t[0..i+1] |-> append(l1, cons(INVALID, nil)) &*&
            t[i+1..size] |-> _;
  @*/


//Replaced by invalid_24/long_none_holds
/* @
lemma void entries_24_mapping_invalid(fixpoint(uint16_t, option<pair<bool, Z> >)
                                        map_func,
                                      list<uint16_t> lst);
  requires length(lst) == TBL_24_MAX_ENTRIES &*&
           lst == repeat_n(nat_of_int(length(lst)), INVALID) &*&
           map_func(INVALID);
  ensures map(map_func, lst) == repeat_n(nat_of_int(length(lst)), none);
@*/

/* @  
lemma void entries_long_mapping_invalid(fixpoint (uint16_t, option<Z>) map_func,
                                        list<uint16_t> lst);
  requires length(lst) == TBL_LONG_MAX_ENTRIES &*&
           lst == repeat_n(nat_of_int(length(lst)), INVALID);
  ensures map(map_func, lst) == repeat_n(nat_of_int(length(lst)), none);
@*/

/*@  
lemma void invalid_is_none24(uint16_t entry, option<pair<bool, Z> > mapped)
  requires entry == INVALID &*& entry_24_mapping(entry) == mapped;
  ensures mapped == none;
  {
    assert entry_24_mapping(INVALID) == none;
  }
  @*/

/*@  
lemma void valid_next_hop24(uint16_t entry, option<pair<bool, Z> > mapped);
  requires entry != INVALID &*& 0 <= entry &*& entry <= 0x7FFF &*&
           entry_24_mapping(entry) == mapped &*& mapped == some(?p) &*&
           p == pair(?b, ?v);
  ensures b == false &*& entry == int_of_Z(v);
@*/

/*@  
lemma void valid_next_bucket_long(uint16_t entry,
                                  option<pair<bool, Z> > mapped);
  requires entry != INVALID &*& true == extract_flag(entry) &*&
           true == valid_entry24(entry) &*&
           entry_24_mapping(entry) == mapped &*& mapped == some(?p) &*&
           p == pair(?b, ?v);
  ensures b == true &*& extract_value(entry) == int_of_Z(v);
@*/

/*@
  lemma void invalid_is_none_long(uint16_t entry, option<Z> mapped)
    requires entry == INVALID &*& entry_long_mapping(entry) == mapped;
    ensures mapped == none;
  {
    assert entry_long_mapping(entry) == none;
  }
  @*/

/*@  
  lemma void valid_next_hop_long(uint16_t entry, option<Z> mapped)
    requires entry != INVALID &*& 0 <= entry &*& entry <= 0x7FFF &*&
             entry_long_mapping(entry) == mapped &*& mapped == some(?v);
    ensures entry == int_of_Z(v);
  {
    Z entryZ = Z_of_uintN(entry, N16);
    assert v == entryZ;
  }
  @*/

/*@  
  lemma void enforce_map_invalid_is_valid(list<uint16_t> entries,
                                          nat size,
                                          fixpoint(uint16_t, bool)
                                            validation_func)
    requires entries == repeat_n(size, INVALID) &*&
             true == forall(entries, check_INVALID) &*&
             true == validation_func(INVALID);
    ensures true == forall(entries, validation_func);
  {
    switch(entries){
      case nil:
      case cons(x, xs): 
        switch(size){
          case zero:
          case succ(n): enforce_map_invalid_is_valid(xs, n, validation_func);
        }
    }
  }
  @*/

/*@
lemma void long_index_extraction_equivalence(uint16_t entry,
                                             option<pair<bool, Z> > mapped);
  requires entry_24_mapping(entry) == mapped;
  ensures (entry & 0xFF) == extract24_value(mapped);
@*/

/*@ 
lemma void long_index_computing_equivalence_on_prefixlen32(uint32_t ipv4,
                                                           uint8_t base_index);
  requires 0 <= ipv4 &*& ipv4 <= 0xffffffff;
  ensures compute_starting_index_long(init_rule(ipv4, 32, 0), base_index) ==
          indexlong_from_ipv4(Z_of_int(ipv4, N32), base_index);
@*/

/*@          
lemma void uint32_equal_are_Z_equal(uint32_t x, Z y);
  requires 0 <= x &*& x <= 0xFFFFFFFF &*& x == int_of_Z(y);
  ensures Z_of_int(x, N32) == y;
@*/

/*@
lemma void set_flag_in_mapped(uint16_t entry, option<pair<bool, Z> > mapped);
  requires 0 <= entry &*& entry < 256 &*&
           entry_24_mapping(entry) == mapped &*& mapped == some(?p) &*&
           p == pair(_, ?z);
  ensures entry_24_mapping(set_flag(entry)) == set_flag_entry(mapped) &*& 
          set_flag_entry(mapped) == some(?p2) &*& p2 == pair(true, z) &*&
          true == valid_entry24(set_flag(entry));
@*/

/*@          
lemma void length_update_n_tbl_24(list<option<pair<bool, Z> > > l,
                                  uint32_t first_index,
                                  uint32_t rule_size,
                                  option<pair<bool, Z> > entry);
  requires 0 <= first_index &*& first_index < length(l) &*& 0 < rule_size &*&
          first_index+rule_size <= length(l);
  ensures length(l) == length(update_n_tbl_24(l, first_index,
                                              nat_of_int(rule_size), entry));
@*/

/*@  
lemma void update24_list_is_update_map(list<option<pair<bool,Z> > > map,
                                       list<uint16_t> entries,
                                       uint32_t first_index, uint32_t index,
                                       uint16_t value);
  requires true == forall(entries, valid_entry24) &*&
           map(entry_24_mapping, entries) ==
           update_n_tbl_24(map, first_index, nat_of_int(index-first_index),
                           entry_24_mapping(value)) &*&
           true == valid_entry24(value);
  ensures map(entry_24_mapping, update(index, value, entries)) ==
          update_n_tbl_24(map, first_index, nat_of_int(index-first_index+1),
                          entry_24_mapping(value));
@*/

/*@                          
  lemma void length_update_n_tbl_long(list<option<Z> > l, uint32_t first_index,
                                    uint32_t rule_size, option<Z> entry);
    requires 0 <= first_index &*& first_index < length(l) &*& 0 < rule_size &*&
            first_index+rule_size <= length(l);
    ensures length(l) ==
            length(update_n_tbl_long(l, first_index, nat_of_int(rule_size),
                                     entry));
  @*/

/*@  
lemma void update_long_list_is_update_map(list<option<Z> > map,
                                          list<uint16_t> entries,
                                          uint32_t first_index, uint32_t index,
                                          uint16_t value);
  requires true == forall(entries, valid_entry_long) &*&
           map(entry_long_mapping, entries) ==
           update_n_tbl_long(map, first_index, nat_of_int(index-first_index),
                             entry_long_mapping(value)) &*&
           true == valid_entry_long(value);
  ensures map(entry_long_mapping, update(index, value, entries)) ==
          update_n_tbl_long(map, first_index, nat_of_int(index-first_index+1),
                          entry_long_mapping(value));
@*/

/*@
  lemma void value24_extraction_equivalence(uint16_t entry,
                                            option<pair<bool, Z> > mapped);
    requires 0 <= extract_value(entry) &*&
             extract_value(entry) <= 0xFF &*&
             extract_flag(entry) == true &*&
             valid_entry24(entry) == true &*&
             entry_24_mapping(entry) == mapped;
    ensures extract_value(entry) == extract24_value(mapped);
  /*{
    
    Z entry_valZ = Z_of_uintN(extract_value(entry), N16);
    
    option<pair<bool, Z> > mapped_entry =
                           some(pair(extract_flag(entry),
                                     entry_valZ));
    
    assert mapped == mapped_entry;
  }*/
  @*/

/*@  
lemma void first_index_depends_on_prefixlen(lpm_rule new_rule,
                                            uint8_t base_index,
                                            uint8_t prefixlen);
  requires 0 <= base_index &*& base_index < 256 &*& 24 <= prefixlen &*&
           prefixlen <= 32;
  ensures compute_starting_index_long(new_rule, base_index) <= (0xFFFF+1)-
          compute_rule_size(prefixlen);
@*/

/*@
  lemma void invalid_24_none_holds(list<uint16_t> entries, list<option<pair<bool, Z> > > mapped, nat size);
    requires entries == repeat_n(nat_of_int(TBL_24_MAX_ENTRIES), INVALID) &*&
             mapped == repeat_n(nat_of_int(TBL_24_MAX_ENTRIES), none) &*&
             true == forall(entries, check_INVALID) &*&
             true == forall(mapped, is_none) &*&
             entry_24_mapping(INVALID) == none;
    ensures map(entry_24_mapping, entries) == mapped;
    @*/
/*@
  lemma void invalid_long_none_holds(list<uint16_t> entries, list<option<Z > > mapped, nat size);
    requires entries == repeat_n(nat_of_int(TBL_LONG_MAX_ENTRIES), INVALID) &*&
             mapped == repeat_n(nat_of_int(TBL_LONG_MAX_ENTRIES), none) &*&
             true == forall(entries, check_INVALID) &*&
             true == forall(mapped, is_none) &*&
             entry_long_mapping(INVALID) == none;
    ensures map(entry_long_mapping, entries) == mapped;
    @*/
  /*{
    switch(size){
      case zero:
      case succ(n):
        elem_is_valid(entries, check_INVALID, int_of_nat(n));
        elem_is_valid(mapped, is_none,int_of_nat(n));
        assert entry_24_mapping(nth(int_of_nat(n), entries)) == nth(int_of_nat(n), mapped);
        invalid24_none_holds(entries, mapped, n);
    }
  }* /
  @*/

//Z3 STALLS I DON'T KNOW WHY ON long_index_computing_equivalence_on_prefixlen32
/*{  
  Z ipv4Z = Z_of_uintN(ipv4, N32);
  Z mask32 = Z_of_uintN(0xFFFFFFFF, N32);
  assert mask32_from_prefixlen(32) == mask32;
   
  bitand_def(ipv4, ipv4Z, 0xFFFFFFFF, mask32);
  Z andRes = Z_and(ipv4Z, mask32);
   
  assert ipv4Z == andRes;
}*/

struct tbl{
  uint16_t* tbl_24;
  uint16_t* tbl_long;
  uint16_t  tbl_long_index;
};

void fill_invalid(uint16_t *t, uint32_t size)
//@ requires t[0..size] |-> _ &*& size > 0;
/*@ ensures t[0.. size] |-> ?inv_list &*&
            inv_list == repeat_n(nat_of_int(size), INVALID) &*&
            true == forall(inv_list, check_INVALID);
@*/
{ 
  for(uint32_t i = 0; ; i++)
  /*@ invariant 0 <= i &*& i <= size &*&
                t[0..i] |-> ?updated &*&
                updated == repeat_n(nat_of_int(i), INVALID) &*&
                true == forall(updated, check_INVALID) &*&
                t[i..size] |-> _;
  @*/
  {
    if(i == size){
      break;
    } 
    
    t[i] = INVALID;
    //@ new_invalid(t, i, size);
    //@ repeat_n_append(updated, INVALID, i);
    //@ forall_append(updated, cons(INVALID, nil), check_INVALID);
  }
  //@ repeat_n_length(nat_of_int(size), INVALID);
  
  //@ assert t[0..size] |-> ?new;
  //@ assert length(new) == length(repeat_n(nat_of_int(size), INVALID));
  //@ assert true == forall(new, check_INVALID); 
}

uint32_t build_mask_from_prefixlen(uint8_t prefixlen)
//@ requires prefixlen <= 32;
//@ ensures result == int_of_Z(mask32_from_prefixlen(prefixlen));
{
  uint32_t ip_masks[33] = { 0x00000000, 0x80000000, 0xC0000000, 0xE0000000,
                            0xF0000000, 0xF8000000, 0xFC000000, 0xFE000000, 
                            0xFF000000, 0xFF800000, 0xFFC00000, 0xFFE00000, 
                            0xFFF00000, 0xFFF80000, 0xFFFC0000, 0xFFFE0000,
                            0xFFFF0000, 0xFFFF8000, 0xFFFFC000, 0xFFFFE000, 
                            0xFFFFF000, 0xFFFFF800, 0xFFFFFC00, 0xFFFFFE00,
                            0xFFFFFF00, 0xFFFFFF80, 0xFFFFFFC0, 0xFFFFFFE0,
                            0xFFFFFFF0, 0xFFFFFFF8, 0xFFFFFFFC, 0xFFFFFFFE,
                            0xFFFFFFFF};

  return ip_masks[prefixlen];
}

/**
 * Extract the 24 MSB of an uint8_t array and returns them
 */
uint32_t tbl_24_extract_first_index(uint32_t data)
//@ requires true;
/*@ ensures 0 <= result &*& result < pow_nat(2, nat_of_int(24)) &*&
            result == index24_from_ipv4(Z_of_int(data, N32));

@*/
{
  //@ Z d = Z_of_uintN(data, N32);
  //@ shiftright_def(data, d, N8);
  //@ shiftright_limits(data, N32, N8);
  uint32_t res = data >> BYTE_SIZE;
  //@ assert res == int_of_Z(Z_shiftright(d, N8));
  return res;
}


/**
 * Computes how many entries the rule will take
 */
uint32_t compute_rule_size(uint8_t prefixlen)
//@ requires prefixlen <= 32;
/*@ ensures result == compute_rule_size(prefixlen) &*&
            prefixlen < 24 ? 
              result <= pow_nat(2, nat_of_int(24))
            : 
              result <= pow_nat(2, N8);
@*/
{	
  if(prefixlen < 24){
    uint32_t res[24] = { 0x1000000, 0x800000, 0x400000, 0x200000, 0x100000,
                         0x80000, 0x40000, 0x20000, 0x10000, 0x8000, 0x4000,
                         0x2000, 0x1000, 0x800, 0x400, 0x200, 0x100 ,0x80,
                         0x40, 0x20, 0x10, 0x8, 0x4, 0x2};
    uint32_t v = res[prefixlen];
    return v;
  }else{
    uint32_t res[9] = {0x100 ,0x80, 0x40, 0x20, 0x10, 0x8, 0x4, 0x2, 0x1};
    uint32_t v = res[prefixlen-24];
    return v;
  }
}

bool tbl_24_entry_flag(uint16_t entry)
/*@ requires entry != INVALID &*& true == valid_entry24(entry) &*&
    entry_24_mapping(entry) == some(?p) &*& p == pair(?b, _);
@*/

//@ ensures result == extract_flag(entry) &*& result == b;
{
  return (entry >> 15) == 1;
}



uint16_t tbl_24_entry_set_flag(uint16_t entry)
//@ requires 0 <= entry &*& entry < 256;
/*@ ensures result == set_flag(entry) &*& 
            true == extract_flag(result) &*&
            true == valid_entry24(result) &*&
            fst(get_someOption24(entry_24_mapping(result))) == true &*&
            snd(get_someOption24(entry_24_mapping(result))) ==
            Z_of_int(entry, N16);
@*/
{
  //@ bitor_limits(entry, TBL_24_FLAG_MASK, N16);
  uint16_t res = (uint16_t)(entry | TBL_24_FLAG_MASK);
  //@ Z mask = Z_of_uintN(TBL_24_FLAG_MASK, N16);
  //@ Z val = Z_of_uintN(entry, N16);
  //@ bitor_def(entry, val, TBL_24_FLAG_MASK, mask);
  
  //Prove that masking with 0x8000 begins with a one
  //@ flag_mask_or_x_begins_with_one(entry);
  
  //Prove that masking with 0x8000 does not affect the 15 LSB
  //@ flag_mask_or_x_not_affect_15LSB(entry);

  return res;
}


uint16_t tbl_long_extract_first_index(uint32_t data, uint8_t prefixlen,
                                      uint8_t base_index)
/*@ requires 0 <= base_index &*& base_index < TBL_LONG_OFFSET_MAX &*&
             0 <= prefixlen &*& prefixlen <= 32;
@*/
/*@ ensures result ==
            compute_starting_index_long(init_rule(data, prefixlen, 0),
                                        base_index) &*&
            0 <= result &*&
            result <= 0xFFFF;//dummy route, unused
@*/
{   
  //@ lpm_rule rule = init_rule(data, prefixlen, 0); //any route is OK
  
  uint32_t mask = build_mask_from_prefixlen(prefixlen);
  //@ Z maskZ = Z_of_uintN(mask, N32);
  //@ Z d = Z_of_uintN(data, N32);
  //@ bitand_def(data, d, mask, maskZ);
  uint32_t masked_data = data & mask;
  /*@ assert int_of_Z(Z_and(d, mask32_from_prefixlen(prefixlen))) ==
             masked_data;
  @*/
  //@ bitand_limits(data, 0xFF, N32);
  //@ Z masked_dataZ = Z_of_uintN(masked_data, N32);
  //@ Z byte_mask = Z_of_uintN(0xFF, N8);
  //@ bitand_def(masked_data, masked_dataZ, 0xFF, byte_mask);
  uint8_t last_byte = (uint8_t)(masked_data & 0xFF);
  //@ assert (masked_data & 0xFF) == last_byte;
  
  uint16_t res = (uint16_t)(base_index*(uint16_t)TBL_LONG_FACTOR + last_byte);
    
  return res;
}

struct tbl* tbl_allocate()
//@ requires true;
/*@ ensures result == 0 ? 
      true 
    : 
      table(result, dir_init());
@*/
{	
  struct tbl* _tbl = malloc(sizeof(struct tbl));
  if(_tbl == 0){
    return 0;
  }
    
  uint16_t* tbl_24 = (uint16_t*) malloc(TBL_24_MAX_ENTRIES *
                                        sizeof(uint16_t));
  if(tbl_24 == 0){
    free(_tbl);
    return 0;
  }
    
  uint16_t* tbl_long = (uint16_t*) malloc(TBL_LONG_MAX_ENTRIES *
                                          sizeof(uint16_t));
  if(tbl_long == 0){
    free(tbl_24);
    free(_tbl);
    return 0;
  }
   
  //Set every element of the array to INVALID
  fill_invalid(tbl_24, TBL_24_MAX_ENTRIES);
  fill_invalid(tbl_long, TBL_LONG_MAX_ENTRIES);

  /*@ assert tbl_24[0..TBL_24_MAX_ENTRIES] |->
      repeat_n(nat_of_int(TBL_24_MAX_ENTRIES), INVALID);
  @*/
  /*@
      assert tbl_long[0..TBL_LONG_MAX_ENTRIES] |->
      repeat_n(nat_of_int(TBL_LONG_MAX_ENTRIES), INVALID);
  @*/
    
  _tbl->tbl_24 = tbl_24;
  _tbl->tbl_long = tbl_long;
  uint16_t tbl_long_first_index = 0;
  _tbl->tbl_long_index = tbl_long_first_index;
  
  //@ assert ushorts(tbl_24, TBL_24_MAX_ENTRIES, ?t_24);
  //@ assert ushorts(tbl_long, TBL_LONG_MAX_ENTRIES, ?t_l);
  
  //@ assert t_24 == repeat_n(nat_of_int(TBL_24_MAX_ENTRIES), INVALID);
  //@ assert t_l == repeat_n(nat_of_int(TBL_LONG_MAX_ENTRIES), INVALID);
  //@ assert entry_24_mapping(INVALID) == none;
  
  //@ list<option<pair<bool, Z> > > map_24 = repeat_n(nat_of_int(TBL_24_MAX_ENTRIES), none);
  //@ list<option<Z> > map_l = repeat_n(nat_of_int(TBL_LONG_MAX_ENTRIES), none);
  
  //@ map_preserves_length(entry_24_mapping, t_24);
  //@ map_preserves_length(entry_long_mapping, t_l);
  
  //@ repeat_n_forall(map_24, nat_of_int(TBL_24_MAX_ENTRIES), none, is_none);
  //@ repeat_n_forall(map_l, nat_of_int(TBL_LONG_MAX_ENTRIES), none, is_none);
  
  //@ invalid_24_none_holds(t_24, map_24, nat_of_int(TBL_24_MAX_ENTRIES));
  //@ invalid_long_none_holds(t_l, map_l, nat_of_int(TBL_LONG_MAX_ENTRIES));
  
  //@ assert map_24 == map(entry_24_mapping, t_24);
  //@ assert map_l == map(entry_long_mapping, t_l);
  
  //Prove that a list of INVALID is valid
  //@ enforce_map_invalid_is_valid(t_24, nat_of_int(TBL_24_MAX_ENTRIES), valid_entry24);
  //@ enforce_map_invalid_is_valid(t_l, nat_of_int(TBL_LONG_MAX_ENTRIES), valid_entry_long);
  
  /*@ close table(_tbl, build_tables(t_24, t_l, tbl_long_first_index));
  @*/

  return _tbl;
}


void tbl_free(struct tbl *_tbl)
//@ requires table(_tbl, _);
//@ ensures true;
{
  //@ open table(_tbl, _);
  free(_tbl->tbl_24);
  free(_tbl->tbl_long);
  free(_tbl);
}


int tbl_update_elem(struct tbl *_tbl, struct key *_key)
/*@ requires table(_tbl, ?dir) &*&
              key(_key, ?ipv4, ?plen, ?route);
@*/
/*@ ensures table(_tbl,
                  add_rule(dir,
                           init_rule(ipv4, plen, route)
                  )
            )
            &*& key(_key, ipv4, plen, route);
@*/
{
  //@ open key(_key, ipv4, plen, route);
  //@ open table(_tbl, dir);
  
  uint8_t prefixlen = _key->prefixlen;
  uint32_t data = _key->data;
  //@ Z d = Z_of_uintN(data, N32);
  uint16_t value = _key->route;
  uint16_t *tbl_24 = _tbl->tbl_24;
  uint16_t *tbl_long = _tbl->tbl_long;
  
  //@ assert ushorts(tbl_24, TBL_24_MAX_ENTRIES, ?t_24);
  //@ assert ushorts(tbl_long, TBL_LONG_MAX_ENTRIES, ?t_l);
  
  //@ assert dir == tables(?map_24, ?map_l, ?long_index);

  //@ lpm_rule new_rule = init_rule(data, prefixlen, value);

  if(prefixlen > TBL_PLEN_MAX || value > MAX_NEXT_HOP_VALUE){
    //@ close key(_key, ipv4, plen, route);
    //@ close table(_tbl, dir);
    return -1;
  }
  uint32_t mask = build_mask_from_prefixlen(prefixlen);
  //@ Z maskZ = mask32_from_prefixlen(prefixlen);
  //@ assert mask == int_of_Z(maskZ);
  
  uint32_t masked_data = data & mask;
  //@ bitand_def(data, d, mask, maskZ);
  //@ Z masked_dataZ = Z_and(d, maskZ);
  //Show that if two uint32_t are equal, then their respective Z values
  // are also equal
  //@ uint32_equal_are_Z_equal(masked_data, masked_dataZ);
  //@ assert masked_data == int_of_Z(masked_dataZ);
  //@ assert (Z_of_int(masked_data, N32) == masked_dataZ);

  //If prefixlen is smaller than 24, simply store the value in tbl_24
  if(prefixlen < 24){

    uint32_t first_index = tbl_24_extract_first_index(masked_data);
    //@ assert first_index == index24_from_ipv4(masked_dataZ);
    //@ assert first_index == compute_starting_index_24(new_rule);
    uint32_t rule_size = compute_rule_size(prefixlen);
    //@ assert rule_size == compute_rule_size(prefixlen);
    uint32_t last_index = first_index + rule_size;

    //@ assert last_index <= length(t_24);
    
    //@ assert INVALID != value;
    //@ assert true == valid_entry24(value);
    //@ assert route == value;
    //@ extract_value_is_value(value);
    //@ assert route == extract_value(route);
    /*@ assert some(pair(false, Z_of_int(route, N16))) ==
               entry_24_mapping(value);
    @*/
    
    /*@ list<option<pair<bool, Z> > > updated_map =
        update_n_tbl_24(map_24, first_index,nat_of_int(rule_size),
                        entry_24_mapping(value));
    @*/
    
    /*@ length_update_n_tbl_24(map_24, first_index, rule_size,
                               entry_24_mapping(value));
    @*/
    
    //@ assert length(updated_map) == length(map_24);
    
    //fill all entries between [first index and last index[ with value
    for(uint32_t i = first_index; ; i++)
    /*@ invariant 0 <= i &*& i <= last_index &*&
                  tbl_24[0..TBL_24_MAX_ENTRIES] |-> ?updated &*&
                  true == forall(updated, valid_entry24) &*&
                  map(entry_24_mapping, updated) ==
                  update_n_tbl_24(map_24, first_index,
                                  nat_of_int(i-first_index),
                                  entry_24_mapping(value));
    @*/
    {
      if(i == last_index){
        break;
      }
      
      //@ assert ushorts(tbl_24, TBL_24_MAX_ENTRIES, ?before);
      //@ forall_update(updated, valid_entry24, i, value);
      //@ update24_list_is_update_map(map_24, updated, first_index, i, value);
      tbl_24[i] = value;
      //@ assert ushorts(tbl_24, TBL_24_MAX_ENTRIES, ?after);
      //@ assert after == update(i, value, before);
    }
    
    
    //@ assert tbl_24[0..TBL_24_MAX_ENTRIES] |-> ?new_t_24;
    //@ assert length(new_t_24) == length(updated_map);
    //@ assert (map(entry_24_mapping, new_t_24) == updated_map);


    //@ assert (build_tables(new_t_24,t_l,long_index)==add_rule(dir, new_rule));
    //@ close table(_tbl, build_tables(new_t_24, t_l, long_index));
  } else {
  //If the prefixlen is not smaller than 24, we have to store the value
  //in tbl_long.
  
    //Check the tbl_24 entry corresponding to the key. If it already has a
    //flag set to 1, use the stored value as base index, otherwise get a new
    //index and store it in the tbl_24
    uint8_t base_index;
    uint32_t tbl_24_index = tbl_24_extract_first_index(data);
    //@ assert tbl_24_index == index24_from_ipv4(d);
    //@ assert tbl_24_index == compute_starting_index_24(new_rule);
      
    uint16_t tbl_24_value = tbl_24[tbl_24_index];
    //Prove that the value retrieved by lookup_tbl_24 is the mapped value
    //retrieved by tbl_24[index]

    //@ nth_map(tbl_24_index, entry_24_mapping, t_24);
    //@ assert entry_24_mapping(tbl_24_value)==lookup_tbl_24(tbl_24_index, dir);
    //@ option<pair<bool, Z> > value24 = lookup_tbl_24(tbl_24_index, dir);
  
    //Prove that the retrieved elem is valid
    //@ forall_nth(t_24, valid_entry24, tbl_24_index);
    
    bool need_new_index;
    uint16_t new_long_index;
    
    if(tbl_24_value == INVALID){
      need_new_index = true;
      //@ assert value24 == none;
      //@ assert need_new_index == is_new_index_needed(value24);
    }else{
      need_new_index = !tbl_24_entry_flag(tbl_24_value);
      //@ assert need_new_index == !extract_flag(tbl_24_value);
      //@ assert value24 == some(?p);
      //@ assert need_new_index == !fst(p);
    }
    
    //@ assert need_new_index == is_new_index_needed(value24);
      
    if(need_new_index){
      if(_tbl->tbl_long_index >= TBL_LONG_OFFSET_MAX){
        //@ assert long_index >= 256;
        printf("No more available index for tbl_long!\n");fflush(stdout);
        //@ close key(_key, ipv4, plen, route);
        //@ close table(_tbl, dir);
        return -1;
		
      }else{
      //generate next index and store it in tbl_24
        base_index = (uint8_t)(_tbl->tbl_long_index);
        //@ assert 0 <= base_index &*& base_index < 256;
        //@ option<pair<bool, Z> > index_for_long=entry_24_mapping(base_index);
        new_long_index = (uint16_t)(_tbl->tbl_long_index + 1);
        _tbl->tbl_long_index = new_long_index;
        // ASSERT THAT THE LIST IS STILL VALID????
        uint16_t new_entry24 = tbl_24_entry_set_flag(base_index);
        //@ flag_mask_or_x_not_affect_15LSB(base_index);
        //@ assert new_entry24 == set_flag(base_index);
        //@ set_flag_in_mapped(base_index, index_for_long);
        /*@ assert entry_24_mapping(new_entry24) ==
                   set_flag_entry(index_for_long);
        @*/
        
        //@ assert INVALID != new_entry24;
        //@ assert true == valid_entry24(new_entry24);
        //@ assert true == extract_flag(new_entry24);
        /*@ assert entry_24_mapping(new_entry24) ==
                   some(pair(true, Z_of_int(base_index, N16)));
        @*/
        
        //@ forall_update(t_24, valid_entry24, tbl_24_index, new_entry24);
        /*@ update24_list_is_update_map(map_24, t_24, tbl_24_index,
                                        tbl_24_index, new_entry24);
        @*/
        tbl_24[tbl_24_index] = new_entry24;
        
        //@ assert tbl_24[0..TBL_24_MAX_ENTRIES] |-> ?updated_t_24;
        /*@ assert map(entry_24_mapping, updated_t_24) ==
                   update_n_tbl_24(map_24, tbl_24_index, N1,
                                   entry_24_mapping(new_entry24));
        @*/
      }      
    }else{
      new_long_index = _tbl->tbl_long_index;
      
      base_index = (uint8_t)(tbl_24_value & 0x7FFF);
      //@ assert entry_24_mapping(tbl_24_value) == value24;
      //@ assert value24 == some(?p);
      //@ assert fst(p) == true;
      
      //@ assert true == valid_entry24(tbl_24_value);
      //@ assert true == extract_flag(tbl_24_value);
      /*@ assert 0 <= extract_value(tbl_24_value) &*&
                 extract_value(tbl_24_value) <= 0xFF;
      @*/
      //@ assert snd(p) == Z_of_int(extract_value(tbl_24_value),N16);
      /*@ assert entry_24_mapping(tbl_24_value) ==
                 lookup_tbl_24(tbl_24_index, dir);
      @*/

      //Show extraction equivalence
      //@ value24_extraction_equivalence(tbl_24_value, value24);
      //@ assert base_index == extract24_value(entry_24_mapping(tbl_24_value));
    }
    
    //@ assert tbl_24[0..TBL_24_MAX_ENTRIES] |-> ?new_t_24;

    //The last byte in data is used as the starting offset for tbl_long
    //indexes
    uint32_t first_index = tbl_long_extract_first_index(data, prefixlen,
                                                        base_index);
    //@ assert first_index == compute_starting_index_long(new_rule, base_index);
    uint32_t rule_size = compute_rule_size(prefixlen);
    //@ assert rule_size == compute_rule_size(prefixlen);
    uint32_t last_index = first_index + rule_size;
    //@ first_index_depends_on_prefixlen(new_rule, base_index, prefixlen);
    //@ assert (last_index <= length(t_l));
    
    //@ assert INVALID != value;
    //@ assert true == valid_entry_long(value);
    //@ assert route == value;
    //@ extract_value_is_value(value);
    //@ assert route == extract_value(route);
    //@ assert some(Z_of_int(route, N16)) == entry_long_mapping(value);
    
    /*@ list<option<Z> > updated_map =
                         update_n_tbl_long(map_l, first_index,
                                           nat_of_int(rule_size),
                                           entry_long_mapping(value));
    @*/
                                                                                                           
    /*@ length_update_n_tbl_long(map_l, first_index, rule_size,
                                 entry_long_mapping(value));
    @*/
    //@ assert length(updated_map) == length(map_l);

    //Store value in tbl_long entries
    for(uint32_t i = first_index; ; i++)
    /*@ invariant 0 <= i &*& i <= last_index &*&
                  tbl_long[0..TBL_LONG_MAX_ENTRIES] |-> ?updated &*&
                  true == forall(updated, valid_entry_long) &*&
                  map(entry_long_mapping, updated) ==
                  update_n_tbl_long(map_l, first_index,
                                    nat_of_int(i-first_index),
                                    entry_long_mapping(value));
    @*/
    { 
      if(i == last_index){
        break;
      }
      //@ forall_update(updated, valid_entry_long, i, value);
      //@ update_long_list_is_update_map(map_l, updated, first_index, i, value);
      tbl_long[i] = value;
    }

    //@ assert tbl_long[0..TBL_LONG_MAX_ENTRIES] |-> ?new_t_l;
    //@ assert length(new_t_l) == length(updated_map);
    //@ assert map(entry_long_mapping, new_t_l) == updated_map;
    
    /*@ assert build_tables(new_t_24, new_t_l, new_long_index) ==
               add_rule(dir, new_rule);
    @*/
    //@ close table(_tbl, build_tables(new_t_24, new_t_l, new_long_index));
  }
  //@ close key(_key, ipv4, plen, route);
  return 0;
}

int tbl_lookup_elem(struct tbl *_tbl, uint32_t data)
//@ requires table(_tbl, ?dir);
/*@ ensures table(_tbl, dir) &*&
            result == lpm_dir_24_8_lookup(Z_of_int(data, N32),dir);
@*/
{

  //@ open table(_tbl, dir);
  uint16_t *tbl_24 = _tbl->tbl_24;
  uint16_t *tbl_long = _tbl->tbl_long;
  
  //@ assert ushorts(tbl_24, TBL_24_MAX_ENTRIES, ?t_24);
  //@ assert ushorts(tbl_long, TBL_LONG_MAX_ENTRIES, ?t_l);
  
  //@ Z d = Z_of_uintN(data, N32);
  //@ assert d == Z_of_int(data, N32);
  
  //get index corresponding to key for tbl_24
  uint32_t index = tbl_24_extract_first_index(data);
  //@ assert index == index24_from_ipv4(d);

  uint16_t value = tbl_24[index];
  //Prove that the value retrieved by lookup_tbl_24 is the mapped value
  //retrieved by tbl_24[index]

  //@ nth_map(index, entry_24_mapping, t_24);
  //@ assert entry_24_mapping(value) == lookup_tbl_24(index, dir);
  //@ option<pair<bool, Z> > value24 = lookup_tbl_24(index, dir);
  
  //Prove that the retrieved elem is valid
  //@ forall_nth(t_24, valid_entry24, index);
	
  if(value != INVALID && tbl_24_entry_flag(value)){
  //the value found in tbl_24 is a base index for an entry in tbl_long,
  //go look at the index corresponding to the key and this base index
    //Prove that the value retrieved by lookup_tbl_24
    //(without the first bit) is 0 <= value <= 0xFF
    //@ valid_next_bucket_long(value, value24);

    // value must be 0 <= value <= 255
    //@ bitand_limits(data, 0xFF, N32);
    uint8_t extracted_index = (uint8_t)(value & 0xFF);
    //@ long_index_extraction_equivalence(value, value24);
    //@ assert extracted_index == extract24_value(value24);
    uint16_t index_long = tbl_long_extract_first_index(data, 32,
                                                       extracted_index);
    //Show that indexlong_from_ipv4 == compute_starting_index_long when
    //the rule has prefixlen == 32
    //@ long_index_computing_equivalence_on_prefixlen32(data, extracted_index);
    uint16_t value_long = tbl_long[index_long];
                                                                  
    //Prove that the value retrieved by lookup_tbl_long is the mapped value
    //retrieved by tbl_24[index]
    //@ nth_map(index_long, entry_long_mapping, t_l);
    //@ assert entry_long_mapping(value_long)==lookup_tbl_long(index_long, dir);
    //@ option<Z> value_l = lookup_tbl_long(index_long, dir);
    
    //Prove that the retrieved elem is valid
    //@ forall_nth(t_l, valid_entry_long, index_long);

    //@ close table(_tbl, dir);
    
    if(value_long == INVALID){
      //@ assert value_long == lpm_dir_24_8_lookup(d,dir);
      //@ invalid_is_none_long(value_long, value_l);
      return INVALID;
    }else{
      //@ valid_next_hop_long(value_long, value_l);
      return value_long;
    }
  } else {
  //the value found in tbl_24 is the next hop, just return it
    //@ close table(_tbl, dir);
    
    if(value == INVALID){
      //@ invalid_is_none24(value, value24);
      return INVALID;
    }else{
    //@ valid_next_hop24(value, value24);
      return value;
    }
  }
}