#include "lpm-dir-24-8.h"

//@ #include "lpm-dir-24-8-lemmas.gh"

/*@
  predicate table(struct lpm* t, dir_24_8 dir) = 
    malloc_block_lpm(t) &*&
    t->lpm_24 |-> ?lpm_24 &*& t->lpm_long |-> ?lpm_long &*&
    t->lpm_long_index |-> ?long_index &*&
    malloc_block_ushorts(lpm_24, lpm_24_MAX_ENTRIES) &*&
    malloc_block_ushorts(lpm_long, lpm_LONG_MAX_ENTRIES) &*&
    lpm_24[0..lpm_24_MAX_ENTRIES] |-> ?tt_24 &*&
    lpm_long[0..lpm_LONG_MAX_ENTRIES] |-> ?tt_l &*&
    true == forall(tt_24, valid_entry24) &*&
    true == forall(tt_l, valid_entry_long) &*&
    build_tables(tt_24, tt_l, long_index) == dir &*&
    map(entry_24_mapping, tt_24) == dir_lpm24(dir) &*&
    map(entry_long_mapping, tt_l) == dir_lpm_long(dir) &*&
    length(tt_24) == length(dir_lpm24(dir)) &*&
    length(tt_l) == length(dir_lpm_long(dir)) &*&
    long_index >= 0 &*& long_index <= lpm_LONG_FACTOR;
  @*/

/*@
  predicate rule(struct rule* r; uint32_t ipv4, uint8_t prefixlen,
                uint16_t route) = 
    malloc_block_rule(r) &*&
    r->ipv4 |-> ipv4 &*&
    r->prefixlen |-> prefixlen &*&
    r->route |-> route &*&
    prefixlen >= 0 &*& prefixlen <= 32 &*&
    route != INVALID &*& 0 <= route &*& route <= MAX_NEXT_HOP_VALUE &*&
    false == extract_flag(route) &*&
    true == valid_entry24(route) &*& true == valid_entry_long(route);
  @*/

/*@
  fixpoint bool is_none<t>(option<t> mapped) {
    return mapped == none;
  }
  @*/

/*@
  fixpoint bool check_INVALID(uint16_t current) {
    return current == INVALID;
  }
  @*/

/*@
  lemma void map_update<t, u>(int i, t y, list<t> xs, fixpoint(t, u) f)
    requires 0 <= i &*& i < length(xs);
    ensures map(f, update(i, y, xs)) == update(i, f(y), map(f, xs));
  {
    switch(xs) {
      case nil:
      case cons(x, xs0):
        if (i != 0) {
          map_update(i-1, y, xs0, f);
        }
    }
  }
  @*/
    
/*@
  lemma void map_update_n<t, u>(int start, nat n, t y, list<t> xs,
                                fixpoint(t, u) f)
    requires 0 <= start &*& start + int_of_nat(n) <= length(xs);
    ensures map(f, update_n(xs, start, n, y)) ==
            update_n(map(f, xs), start, n, f(y));
  {
    switch(n) {
      case zero:
      case succ(n0):
        list<t> updated = update(start, y, xs);
        map_update(start, y, xs, f);
        map_update_n(start+1, n0, y, updated, f);
    }
  }
  @*/

/*@
  lemma void loop_update_n<t>(int start, nat count, t y, list<t> xs)
    requires true;
    ensures update(start + int_of_nat(count), y,
                   update_n(xs, start, count, y)) ==
            update_n(xs, start, succ(count), y);
  {
    switch(count) {
      case zero:
      case succ(n): 
        loop_update_n(start+1, n, y, update(start, y, xs));
    }
  }
  @*/
  
/*@
  lemma void repeat_n_forall<t>(nat size, t e, fixpoint(t, bool) p)
    requires true == p(e);
    ensures true == forall(repeat_n(size, e), p); 
  { 
     switch(size) {
       case zero:
       case succ(n): repeat_n_forall(n, e, p);
     }
  }
  @*/

/*@
  lemma void repeat_n_append<t>(t e, nat size)
    requires true;
    ensures append(repeat_n(size, e), cons(e, nil)) == repeat_n(succ(size), e);
  {
    switch(size) {
      case zero:
      case succ(n): repeat_n_append(e, n);
    }
  }
  @*/

/*@
  lemma void new_invalid(uint16_t *t, uint32_t i, nat j, uint32_t size)
    requires t[(i - int_of_nat(j))..i] |-> repeat_n(j, INVALID) &*&
             i < size &*&
             int_of_nat(j) <= i &*&
             t[i] |-> INVALID &*&
             t[i+1..size] |-> _;
    ensures t[(i - int_of_nat(j))..i+1] |->
            append(repeat_n(j, INVALID), cons(INVALID, nil)) &*&
            t[i+1..size] |-> _;
  {
    switch(j) {
      case zero:
      case succ(n): 
        assert int_of_nat(succ(n)) == int_of_nat(n)+1;
        assert u_short_integer(t+(i - int_of_nat(n))-1, INVALID);
        new_invalid(t, i, n, size);
        assert ushorts(t+(i - int_of_nat(n)), int_of_nat(n)+1,
                       append(repeat_n(n, INVALID), cons(INVALID, nil)));
        assert ushorts(t+(i - int_of_nat(n))-1, int_of_nat(n)+2,
                       cons(INVALID,
                            append(repeat_n(n, INVALID), cons(INVALID, nil))));
        assert t[(i - int_of_nat(n))-1..i+1] |->
               cons(INVALID,  append(repeat_n(n, INVALID), cons(INVALID, nil)));
        assert t[(i - int_of_nat(n))-1..i+1] |->
               append(cons(INVALID, repeat_n(n, INVALID)), cons(INVALID, nil));
        assert t[(i - int_of_nat(n))-1..i+1] |->
               append(repeat_n(succ(n), INVALID), cons(INVALID, nil));
        assert t[(i - int_of_nat(succ(n)))..i+1] |->
               append(repeat_n(succ(n), INVALID), cons(INVALID, nil));
    }
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
    switch(entries) {
      case nil:
      case cons(x, xs): 
        switch(size) {
          case zero:
          case succ(n): enforce_map_invalid_is_valid(xs, n, validation_func);
        }
    }
  }
  @*/

/*@
  lemma void invalid_24_none_holds(nat size)
    requires entry_24_mapping(INVALID) == none;
    ensures map(entry_24_mapping, repeat_n(size, INVALID)) ==
            repeat_n(size, none);
    {
      switch(size) {
        case zero:
        case succ(n): invalid_24_none_holds(n);
      }
    }
  @*/

/*@
  lemma void invalid_long_none_holds(nat size)
    requires entry_long_mapping(INVALID) == none;
    ensures map(entry_long_mapping, repeat_n(size, INVALID)) ==
            repeat_n(size, none); 
  {
    switch(size) {
      case zero:
      case succ(n): invalid_long_none_holds(n);
    }
  }
  @*/

struct lpm {
  uint16_t* lpm_24;
  uint16_t* lpm_long;
  uint16_t  lpm_long_index;
};

void fill_invalid(uint16_t *t, uint32_t size)
//@ requires t[0..size] |-> _ &*& size > 0;
/*@ ensures t[0.. size] |-> ?inv_list &*&
            inv_list == repeat_n(nat_of_int(size), INVALID) &*&
            true == forall(inv_list, check_INVALID); @*/
{ 
  for (uint32_t i = 0; ; i++)
  /*@ invariant 0 <= i &*& i <= size &*&
                t[0..i] |-> ?updated &*&
                updated == repeat_n(nat_of_int(i), INVALID) &*&
                true == forall(updated, check_INVALID) &*&
                t[i..size] |-> _; @*/
  {
    if (i == size) {
      break;
    } 
    
    t[i] = INVALID;
    //@ new_invalid(t, i, nat_of_int(i), size);
    //@ repeat_n_append(INVALID, nat_of_int(i));
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
uint32_t lpm_24_extract_first_index(uint32_t data)
//@ requires true;
/*@ ensures 0 <= result &*& result < pow_nat(2, nat_of_int(24)) &*&
            result == index24_from_ipv4(Z_of_int(data, N32)); @*/
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
            prefixlen < 25 ? 
              result == pow_nat(2, nat_of_int(24-prefixlen))
            : 
              result == pow_nat(2, nat_of_int(32-prefixlen)); @*/
{	
  if (prefixlen < 25) {
    uint32_t res[25] = { 0x1000000, 0x800000, 0x400000, 0x200000, 0x100000,
                         0x80000,   0x40000,  0x20000,  0x10000,  0x8000,
                         0x4000,    0x2000,   0x1000,   0x800,    0x400,
                         0x200,     0x100 ,   0x80,     0x40,     0x20,
                         0x10,      0x8,      0x4,      0x2,      0x1};
    uint32_t v = res[prefixlen];
    return v;
  } else {
    uint32_t res[8] = {0x80, 0x40, 0x20, 0x10, 0x8, 0x4, 0x2, 0x1};
    uint32_t v = res[prefixlen-25];
    return v;
  }
}

bool lpm_24_entry_flag(uint16_t entry)
/*@ requires entry != INVALID &*& true == valid_entry24(entry) &*&
             entry_24_mapping(entry) == some(?p) &*& p == pair(?b, _); @*/
//@ ensures result == extract_flag(entry) &*& result == b;
{
  return (entry >> 15) == 1;
}



uint16_t lpm_24_entry_set_flag(uint16_t entry)
//@ requires 0 <= entry &*& entry < 256;
/*@ ensures result == set_flag(entry) &*& 
            true == extract_flag(result) &*&
            true == valid_entry24(result) &*&
            fst(get_someOption24(entry_24_mapping(result))) == true &*&
            snd(get_someOption24(entry_24_mapping(result))) ==
            Z_of_int(entry, N16); @*/
{
  //@ bitor_limits(entry, lpm_24_FLAG_MASK, N16);
  uint16_t res = (uint16_t)(entry | lpm_24_FLAG_MASK);
  //@ Z mask = Z_of_uintN(lpm_24_FLAG_MASK, N16);
  //@ Z val = Z_of_uintN(entry, N16);
  //@ bitor_def(entry, val, lpm_24_FLAG_MASK, mask);
  
  //Prove that masking with 0x8000 begins with a one
  //@ flag_mask_or_x_begins_with_one(entry);
  
  //Prove that masking with 0x8000 does not affect the 15 LSB
  //@ flag_mask_or_x_not_affect_15LSB(entry);

  return res;
}

uint16_t lpm_long_extract_first_index(uint32_t data, uint8_t prefixlen,
                                      uint8_t base_index)
/*@ requires 0 <= base_index &*& base_index < lpm_LONG_OFFSET_MAX &*&
             0 <= prefixlen &*& prefixlen <= 32; @*/
/*@ ensures result ==
            compute_starting_index_long(init_rule(data, prefixlen, 0),
                                        base_index) &*&
            0 <= result &*&
            result <= 0xFFFF; @*/ //dummy route, unused
{   
  //@ lpm_rule rule = init_rule(data, prefixlen, 0); //any route is OK
  
  uint32_t mask = build_mask_from_prefixlen(prefixlen);
  //@ Z maskZ = Z_of_uintN(mask, N32);
  //@ Z d = Z_of_uintN(data, N32);
  //@ bitand_def(data, d, mask, maskZ);
  uint32_t masked_data = data & mask;

  //@ bitand_limits(data, 0xFF, N32);
  //@ Z masked_dataZ = Z_of_uintN(masked_data, N32);
  //@ Z byte_mask = Z_of_uintN(0xFF, N8);
  //@ bitand_def(masked_data, masked_dataZ, 0xFF, byte_mask);
  uint8_t last_byte = (uint8_t)(masked_data & 0xFF);
  //@ assert (masked_data & 0xFF) == last_byte;
  
  uint16_t res = (uint16_t)(base_index*(uint16_t)lpm_LONG_FACTOR + last_byte);
    
  return res;
}

struct lpm* lpm_allocate()
//@ requires true;
/*@ ensures result == 0 ? 
              true 
            : 
              table(result, dir_init()); @*/
{	
  struct lpm* _lpm = malloc(sizeof(struct lpm));
  if (_lpm == 0) {
    return 0;
  }
    
  uint16_t* lpm_24 = (uint16_t*) malloc(lpm_24_MAX_ENTRIES *
                                        sizeof(uint16_t));
  if (lpm_24 == 0) {
    free(_lpm);
    return 0;
  }
    
  uint16_t* lpm_long = (uint16_t*) malloc(lpm_LONG_MAX_ENTRIES *
                                          sizeof(uint16_t));
  if (lpm_long == 0) {
    free(lpm_24);
    free(_lpm);
    return 0;
  }
   
  //Set every element of the array to INVALID
  fill_invalid(lpm_24, lpm_24_MAX_ENTRIES);
  fill_invalid(lpm_long, lpm_LONG_MAX_ENTRIES);

  /*@ assert lpm_24[0..lpm_24_MAX_ENTRIES] |->
      repeat_n(nat_of_int(lpm_24_MAX_ENTRIES), INVALID);
  @*/
  /*@
      assert lpm_long[0..lpm_LONG_MAX_ENTRIES] |->
      repeat_n(nat_of_int(lpm_LONG_MAX_ENTRIES), INVALID);
  @*/
    
  _lpm->lpm_24 = lpm_24;
  _lpm->lpm_long = lpm_long;
  uint16_t lpm_long_first_index = 0;
  _lpm->lpm_long_index = lpm_long_first_index;
  
  //@ assert ushorts(lpm_24, lpm_24_MAX_ENTRIES, ?t_24);
  //@ assert ushorts(lpm_long, lpm_LONG_MAX_ENTRIES, ?t_l);
  
  //@ assert t_24 == repeat_n(nat_of_int(lpm_24_MAX_ENTRIES), INVALID);
  //@ assert t_l == repeat_n(nat_of_int(lpm_LONG_MAX_ENTRIES), INVALID);
  //@ assert entry_24_mapping(INVALID) == none;
  
  /*@ list<option<pair<bool, Z> > > map_24 =
                                    repeat_n(nat_of_int(lpm_24_MAX_ENTRIES),
                                             none);
  @*/
  //@ list<option<Z> > map_l = repeat_n(nat_of_int(lpm_LONG_MAX_ENTRIES), none);
  
  //@ map_preserves_length(entry_24_mapping, t_24);
  //@ map_preserves_length(entry_long_mapping, t_l);
  
  //@ repeat_n_forall(nat_of_int(lpm_24_MAX_ENTRIES), none, is_none);
  //@ repeat_n_forall(nat_of_int(lpm_LONG_MAX_ENTRIES), none, is_none);
  
  //@ invalid_24_none_holds(nat_of_int(lpm_24_MAX_ENTRIES));
  //@ invalid_long_none_holds(nat_of_int(lpm_LONG_MAX_ENTRIES));
  
  //@ assert map_24 == map(entry_24_mapping, t_24);
  //@ assert map_l == map(entry_long_mapping, t_l);
  
  //Prove that a list of INVALID is valid
  /*@ enforce_map_invalid_is_valid(t_24, nat_of_int(lpm_24_MAX_ENTRIES),
                                   valid_entry24);
  @*/

  /*@ enforce_map_invalid_is_valid(t_l, nat_of_int(lpm_LONG_MAX_ENTRIES),
                                   valid_entry_long);
  @*/
  
  /*@ close table(_lpm, build_tables(t_24, t_l, lpm_long_first_index));
  @*/

  return _lpm;
}

void lpm_free(struct lpm *_lpm)
//@ requires table(_lpm, _);
//@ ensures true;
{
  //@ open table(_lpm, _);
  free(_lpm->lpm_24);
  free(_lpm->lpm_long);
  free(_lpm);
}

int lpm_lookup_elem(struct lpm *_lpm, uint32_t ipv4)
//@ requires table(_lpm, ?dir);
/*@ ensures table(_lpm, dir) &*&
            result == lpm_dir_24_8_lookup(Z_of_int(ipv4, N32),dir); @*/
{

  //@ open table(_lpm, dir);
  uint16_t *lpm_24 = _lpm->lpm_24;
  uint16_t *lpm_long = _lpm->lpm_long;
  
  //@ assert ushorts(lpm_24, lpm_24_MAX_ENTRIES, ?t_24);
  //@ assert ushorts(lpm_long, lpm_LONG_MAX_ENTRIES, ?t_l);

  //get index corresponding to key for lpm_24
  uint32_t index = lpm_24_extract_first_index(ipv4);

  uint16_t value = lpm_24[index];
  //Prove that the value retrieved by lookup_lpm_24 is the mapped value
  //retrieved by lpm_24[index]

  //@ nth_map(index, entry_24_mapping, t_24);

  //@ option<pair<bool, Z> > value24 = lookup_lpm_24(index, dir);
  
  //Prove that the retrieved elem is valid
  //@ forall_nth(t_24, valid_entry24, index);
	
  if (value != INVALID && lpm_24_entry_flag(value)) {
  //the value found in lpm_24 is a base index for an entry in lpm_long,
  //go look at the index corresponding to the key and this base index
    //Prove that the value retrieved by lookup_lpm_24
    //(without the first bit) is 0 <= value <= 0xFF
    //@ valid_next_bucket_long(value, value24);

    //@ bitand_limits(ipv4, 0xFF, N32);
    uint8_t extracted_index = (uint8_t)(value & 0xFF);
    //@ long_index_extraction_equivalence(value, value24);
    //@ assert extracted_index == extract24_value(value24);
    uint16_t index_long = lpm_long_extract_first_index(ipv4, 32,
                                                       extracted_index);
    //Show that indexlong_from_ipv4 == compute_starting_index_long when
    //the rule has prefixlen == 32
    //@ long_index_computing_equivalence_on_prefixlen32(ipv4, extracted_index);
    uint16_t value_long = lpm_long[index_long];
                                                                  
    //Prove that the value retrieved by lookup_lpm_long is the mapped value
    //retrieved by lpm_24[index]
    //@ nth_map(index_long, entry_long_mapping, t_l);
    //@ assert entry_long_mapping(value_long)==lookup_lpm_long(index_long, dir);
    //@ option<Z> value_l = lookup_lpm_long(index_long, dir);
    
    //Prove that the retrieved elem is valid
    //@ forall_nth(t_l, valid_entry_long, index_long);

    //@ close table(_lpm, dir);
    
    if (value_long == INVALID) {
      return INVALID;
    } else {
      //@ valid_next_hop_long(value_long, value_l);
      return value_long;
    }
  } else {
  //the value found in lpm_24 is the next hop, just return it
    //@ close table(_lpm, dir);
    
    if (value == INVALID) {
      return INVALID;
    } else {
    //@ valid_next_hop24(value, value24);
      return value;
    }
  }
}

int lpm_update_elem(struct lpm *_lpm, struct rule *_rule)
/*@ requires table(_lpm, ?dir) &*&
              rule(_rule, ?ipv4, ?plen, ?route); @*/
/*@ ensures table(_lpm,
                  add_rule(dir,
                           init_rule(ipv4, plen, route)
                  )
            )
            &*& rule(_rule, ipv4, plen, route); @*/
{
  //@ open rule(_rule, ipv4, plen, route);
  //@ open table(_lpm, dir);
  
  uint8_t prefixlen = _rule->prefixlen;
  uint32_t ip = _rule->ipv4;
  //@ Z d = Z_of_uintN(ip, N32);

  uint16_t value = _rule->route;
  uint16_t *lpm_24 = _lpm->lpm_24;
  uint16_t *lpm_long = _lpm->lpm_long;
  
  //@ assert ushorts(lpm_24, lpm_24_MAX_ENTRIES, ?t_24);
  //@ assert ushorts(lpm_long, lpm_LONG_MAX_ENTRIES, ?t_l);
  
  //@ assert dir == tables(?map_24, ?map_l, ?long_index);

  //@ lpm_rule new_rule = init_rule(ipv4, prefixlen, value);

  uint32_t mask = build_mask_from_prefixlen(prefixlen);
  //@ Z maskZ = mask32_from_prefixlen(prefixlen);
  
  uint32_t masked_ip = ip & mask;
  //@ bitand_def(ip, d, mask, maskZ);
  //@ bitand_limits(ip, mask, N32);
  //@ Z masked_ipZ = Z_and(d, maskZ);
  //Show that if two uint32_t are equal, then their respective Z values
  // are also equal
  //@ Z_and_length(d, maskZ);
  //@ assert (Z_length(Z_and(d, maskZ)) == N32);
  //@ equal_int_equal_Z(masked_ipZ, N32);
  //@ assert int_of_Z(masked_ipZ) == masked_ip;
  //@ assert (masked_ipZ == Z_of_int(masked_ip, N32));

  //If prefixlen is smaller than 24, simply store the value in lpm_24
  if (prefixlen < 25) {

    uint32_t first_index = lpm_24_extract_first_index(masked_ip);
    // @ assert first_index == index24_from_ipv4(masked_ipZ);
    // @ assert first_index == compute_starting_index_24(new_rule);
    uint32_t rule_size = compute_rule_size(prefixlen);
    // @ assert rule_size == pow_nat(2, nat_of_int(24-prefixlen));
    // @ assert rule_size = compute_rule_size(prefixlen);

    uint32_t last_index = first_index + rule_size;

    // @ assert last_index <= length(t_24);
    
    // @ assert INVALID != value;
    // @ assert true == valid_entry24(value);
    // @ assert route == value;
    //@ extract_value_is_value(value);
    
    /*@ list<option<pair<bool, Z> > > updated_map =
        update_n(map_24, first_index,nat_of_int(rule_size),
                        entry_24_mapping(value));
    @*/
    
    /*@list<uint16_t> updated_t =
       update_n(t_24, first_index, nat_of_int(rule_size), value);
    @*/
    
    //fill all entries between [first index and last index[ with value
    for (uint32_t i = first_index; ; i++)
    /*@ invariant first_index <= i &*& i <= last_index &*&
                  lpm_24[0..lpm_24_MAX_ENTRIES] |-> ?updated &*&
                  true == forall(updated, valid_entry24) &*&
                  updated == update_n(t_24, first_index,
                                      nat_of_int(i-first_index),
                                      value); @*/
    {
      if (i == last_index) {
        break;
      }
      
      lpm_24[i] = value;
      
      //@ forall_update(updated, valid_entry24, i, value);
      
      //Prove that the loop is like update_n
      //@ succ_int(i-first_index);
      //@ loop_update_n(first_index, nat_of_int(i-first_index), value, t_24);
    }
    

    //@ assert lpm_24[0..lpm_24_MAX_ENTRIES] |-> ?new_t_24;
    
    //Prove that mapping holds
    /*@ map_update_n(first_index, nat_of_int(rule_size), value,
                     t_24, entry_24_mapping);
    @*/
    
    // @ assert (map(entry_24_mapping, new_t_24) == updated_map);

    //@ close table(_lpm, build_tables(new_t_24, t_l, long_index));
  } else {
  //If the prefixlen is not smaller than 24, we have to store the value
  //in lpm_long.
  
    //Check the lpm_24 entry corresponding to the key. If it already has a
    //flag set to 1, use the stored value as base index, otherwise get a new
    //index and store it in the lpm_24
    uint8_t base_index;
    uint32_t lpm_24_index = lpm_24_extract_first_index(ip);
    // @ assert lpm_24_index == index24_from_ipv4(d);
    // @ assert lpm_24_index == compute_starting_index_24(new_rule);
      
    uint16_t lpm_24_value = lpm_24[lpm_24_index];
    //Prove that the value retrieved by lookup_lpm_24 is the mapped value
    //retrieved by lpm_24[index]

    //@ nth_map(lpm_24_index, entry_24_mapping, t_24);

    //@ option<pair<bool, Z> > value24 = lookup_lpm_24(lpm_24_index, dir);
  
    //Prove that the retrieved elem is valid
    //@ forall_nth(t_24, valid_entry24, lpm_24_index);
    
    bool need_new_index;
    uint16_t new_long_index;
    
    if (lpm_24_value == INVALID) {
      need_new_index = true;
      // @ assert value24 == none;
      // @ assert need_new_index == is_new_index_needed(value24);
    } else {
      need_new_index = !lpm_24_entry_flag(lpm_24_value);
      // @ assert need_new_index == !extract_flag(lpm_24_value);
      // @ assert value24 == some(?p);
      // @ assert need_new_index == !fst(p);
    }
    
    // @ assert need_new_index == is_new_index_needed(value24);
      
    if (need_new_index) {
      if (_lpm->lpm_long_index >= lpm_LONG_OFFSET_MAX) {
        // @ assert long_index >= 256;
        printf("No more available index for lpm_long!\n");
        fflush(stdout);
        //@ close rule(_rule, ipv4, plen, route);
        //@ close table(_lpm, dir);
        return -1;
		
      } else {
      //generate next index and store it in lpm_24
        base_index = (uint8_t)(_lpm->lpm_long_index);
        // @ assert 0 <= base_index &*& base_index < 256;
        //@ option<pair<bool, Z> > index_for_long=entry_24_mapping(base_index);
        new_long_index = (uint16_t)(_lpm->lpm_long_index + 1);
        _lpm->lpm_long_index = new_long_index;

        uint16_t new_entry24 = lpm_24_entry_set_flag(base_index);
        //@ flag_mask_or_x_not_affect_15LSB(base_index);
        // @ assert new_entry24 == set_flag(base_index);
        
        // @ assert INVALID != new_entry24;
        // @ assert true == valid_entry24(new_entry24);
        // @ assert true == extract_flag(new_entry24);
        
        //@ forall_update(t_24, valid_entry24, lpm_24_index, new_entry24);

        //@ map_update(lpm_24_index, new_entry24, t_24, entry_24_mapping);
        lpm_24[lpm_24_index] = new_entry24;
        
        //@ assert lpm_24[0..lpm_24_MAX_ENTRIES] |-> ?updated_t_24;
        /* @ assert map(entry_24_mapping, updated_t_24) ==
                   update_n(map_24, lpm_24_index, N1,
                                   entry_24_mapping(new_entry24));
        @*/
      }      
    } else {
      new_long_index = _lpm->lpm_long_index;
      
      base_index = (uint8_t)(lpm_24_value & 0x7FFF);
      // @ assert entry_24_mapping(lpm_24_value) == value24;
      // @ assert value24 == some(?p);
      // @ assert fst(p) == true;
      
      // @ assert true == valid_entry24(lpm_24_value);
      // @ assert true == extract_flag(lpm_24_value);
      /* @ assert 0 <= extract_value(lpm_24_value) &*&
                 extract_value(lpm_24_value) <= 0xFF;
      @*/
      // @ assert snd(p) == Z_of_int(extract_value(lpm_24_value),N16);
      /*@ assert entry_24_mapping(lpm_24_value) ==
                 lookup_lpm_24(lpm_24_index, dir);
      @*/

      //Show extraction equivalence
      //@ value24_extraction_equivalence(lpm_24_value, value24);
      // @ assert base_index == extract24_value(entry_24_mapping(lpm_24_value));
    }
    
    //@ assert lpm_24[0..lpm_24_MAX_ENTRIES] |-> ?new_t_24;

    //The last byte in data is used as the starting offset for lpm_long
    //indexes
    uint32_t first_index = lpm_long_extract_first_index(ip, prefixlen,
                                                        base_index);

    uint32_t rule_size = compute_rule_size(prefixlen);
    // @ assert rule_size == compute_rule_size(prefixlen);
    uint32_t last_index = first_index + rule_size;
    //@ first_index_depends_on_prefixlen(new_rule, base_index, prefixlen);
    // @ assert (last_index <= length(t_l));
    
    // @ assert INVALID != value;
    // @ assert true == valid_entry_long(value);
    // @ assert route == value;
    //@ extract_value_is_value(value);
    // @ assert route == extract_value(route);
    //@ assert some(Z_of_int(route, N16)) == entry_long_mapping(value);
    
    /*@ list<option<Z> > updated_map =
                         update_n(map_l, first_index,
                                           nat_of_int(rule_size),
                                           entry_long_mapping(value));
    @*/

    // @ assert length(updated_map) == length(map_l);

    //Store value in lpm_long entries
    for (uint32_t i = first_index; ; i++)
    /*@ invariant first_index <= i &*& i <= last_index &*&
                  lpm_long[0..lpm_LONG_MAX_ENTRIES] |-> ?updated &*&
                  true == forall(updated, valid_entry_long) &*&
                  updated == update_n(t_l, first_index, 
                                      nat_of_int(i-first_index),
                                      value); @*/
    { 
      if (i == last_index) {
        break;
      }
      //@ forall_update(updated, valid_entry_long, i, value);
      
      lpm_long[i] = value;
      
      //Prove that the loop is like update_n
      //@ succ_int(i-first_index);
      //@ loop_update_n(first_index, nat_of_int(i-first_index), value, t_l);
    }

    //@ assert lpm_long[0..lpm_LONG_MAX_ENTRIES] |-> ?new_t_l;
    
    //Prove that mapping holds
    /*@ map_update_n(first_index, nat_of_int(rule_size),
                     value, t_l, entry_long_mapping);
    @*/

    //@ assert map(entry_long_mapping, new_t_l) == updated_map;
    
    //@ close table(_lpm, build_tables(new_t_24, new_t_l, new_long_index));
  }
  //@ close rule(_rule, ipv4, plen, route);
  return 0;
}
