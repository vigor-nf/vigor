#include "dir-24-8-basic.h"
//@ #include <nat.gh>
//@ #include <bitops.gh>

/*@
fixpoint bool is_invalid(uint16_t x){
  return x == INVALID;
}
@*/

void fill_invalid(uint16_t *t, uint32_t size)
//@ requires t[0..size] |-> _;
//@ ensures t[0.. size] |-> _;//repeat_n(nat_of_int(size), INVALID);
{

  //@ list<unsigned short> elems = nil;
  
  for(uint32_t i = 0; i < size; i++)
  /*@ invariant 0 <= i &*& i <= size &*&
                true == forall(elems, is_invalid) &*&
                length(elems) == i &*&
                t[0..size] |-> _;
  @*/
  {
    //@ assert i < size; 
    t[i] = INVALID;
    //@ forall_append(elems, cons(INVALID, nil), is_invalid);
    //@ elems = append(elems, cons(INVALID, nil));
  }
}

uint32_t build_mask_from_prefixlen(uint8_t prefixlen)
//@ requires prefixlen <= 32;
//@ ensures result == int_of_Z(mask32_from_prefixlen(prefixlen));
{
  uint32_t ip_masks[33] = { 0x00000000, 0x80000000, 0xC0000000, 0xE0000000, 0xF0000000, 0xF8000000, 0xFC000000, 0xFE000000, 
                            0xFF000000, 0xFF800000, 0xFFC00000, 0xFFE00000, 0xFFF00000, 0xFFF80000, 0xFFFC0000, 0xFFFE0000,
                            0xFFFF0000, 0xFFFF8000, 0xFFFFC000, 0xFFFFE000, 0xFFFFF000, 0xFFFFF800, 0xFFFFFC00, 0xFFFFFE00,
                            0xFFFFFF00, 0xFFFFFF80, 0xFFFFFFC0, 0xFFFFFFE0, 0xFFFFFFF0, 0xFFFFFFF8, 0xFFFFFFFC, 0xFFFFFFFE, 0xFFFFFFFF};

  return ip_masks[prefixlen];
}

/**
 * Extract the 24 MSB of an uint8_t array and returns then in size_t
 */
uint32_t tbl_24_extract_first_index(uint32_t data)
//@ requires true;
/*@ ensures 0 <= result &*& result < pow_nat(2, nat_of_int(24)) &*&
            result == data >> BYTE_SIZE;

@*/
{
  //@ Z d = Z_of_uint32(data);
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
//@ ensures result == compute_rule_size(prefixlen) &*& prefixlen < 24 ? result <= pow_nat(2, nat_of_int(24)) : result <= pow_nat(2, N8);
{	
  if(prefixlen < 24){
    uint32_t res[24] = { 0x1000000, 0x800000, 0x400000, 0x200000, 0x100000, 0x80000, 0x40000, 0x20000, 0x10000,
                         0x8000, 0x4000, 0x2000, 0x1000, 0x800, 0x400, 0x200, 0x100 ,0x80, 0x40, 0x20, 0x10, 0x8, 0x4, 0x2};
    uint32_t v = res[prefixlen];
    return v;
  }else{
    uint32_t res[9] = {0x100 ,0x80, 0x40, 0x20, 0x10, 0x8, 0x4, 0x2, 0x1};
    uint32_t v = res[prefixlen-24];
    return v;
  }
}

bool tbl_24_entry_flag(uint16_t entry)
//@ requires entry_24(entry_24_mapping(entry));
//@ ensures result == extract_flag(entry) &*& entry_24(entry_24_mapping(entry));
{
  return (entry >> 15) == 1;
}

uint16_t tbl_24_entry_set_flag(uint16_t entry)
//@ requires entry_24(entry_24_mapping(entry));
//@ ensures entry_24(entry_24_mapping(result));
{
  //@ open entry_24(entry_24_mapping(entry));
  //@ bitor_limits(entry, TBL_24_FLAG_MASK, N16);
  //@ Z mask = Z_of_uint16(TBL_24_FLAG_MASK);
  //@ Z val = Z_of_uint16(entry);
  //@ bitor_def(entry, val, TBL_24_FLAG_MASK, mask);
  uint16_t res = (uint16_t)(entry | TBL_24_FLAG_MASK);
  //@ close entry_24(entry_24_mapping(res));
  return res;
}


uint16_t tbl_long_extract_first_index(uint32_t data, uint8_t prefixlen, uint8_t base_index)
//@ requires 0 <= base_index &*& base_index < TBL_LONG_OFFSET_MAX &*& 0 <= prefixlen &*& prefixlen <= 32;
//@ ensures result == compute_starting_index_long(init_rule(data, prefixlen, 0), base_index);//dummy route, unused
{   
  
  uint32_t mask = build_mask_from_prefixlen(prefixlen);
  //@ Z maskZ = Z_of_uint32(mask);
  //@ Z d = Z_of_uint32(data); 
  //@ bitand_def(data, d, mask, maskZ);
  uint32_t masked_data = data & mask;
  //@ bitand_limits(data, 0xFF, N32);
  //@ Z masked_dataZ = Z_of_uint32(masked_data);
  //@ Z byte_mask = Z_of_uint8(0xFF);
  //@ bitand_def(masked_data, masked_dataZ, 0xFF, byte_mask);
  uint8_t last_byte = (uint8_t)(masked_data & 0xFF);
    
  return (uint16_t)(base_index * (uint16_t)TBL_LONG_FACTOR + last_byte);
}

struct tbl* tbl_allocate()
//@ requires true;
/*@ ensures result == 0 ? 
      true 
    : 
      table(result, 0, dir_init());

@*/
{	
  struct tbl* _tbl = malloc(sizeof(struct tbl));
  if(_tbl == 0){
    return 0;
  }
    
  uint16_t* tbl_24 = (uint16_t*) malloc(TBL_24_MAX_ENTRIES * sizeof(uint16_t));
  if(tbl_24 == 0){
    free(_tbl);
    return 0;
  }
    
  uint16_t* tbl_long = (uint16_t*) malloc(TBL_LONG_MAX_ENTRIES * sizeof(uint16_t));
  if(tbl_long == 0){
    free(tbl_24);
    free(_tbl);
    return 0;
  }
   
  //@ close ushorts(tbl_24, TBL_24_MAX_ENTRIES, ?t_24);
  //@ close ushorts(tbl_long, TBL_LONG_MAX_ENTRIES, ?t_l);
  
  //Set every element of the array to INVALID
  fill_invalid(tbl_24, TBL_24_MAX_ENTRIES);
  fill_invalid(tbl_long, TBL_LONG_MAX_ENTRIES);
  
  //@ assert forall(t_24, is_invalid);
  //@ assert forall(t_l, is_invalid);
    
  _tbl->tbl_24 = tbl_24;
  _tbl->tbl_long = tbl_long;
  uint16_t tbl_long_first_index = 0;
  _tbl->tbl_long_index = tbl_long_first_index;
  //@ close table(_tbl, tbl_long_first_index, build_tables(t_24, t_l, tbl_long_first_index));

  return _tbl;
}


void tbl_free(struct tbl *_tbl)
//@ requires table(_tbl, _, _);
//@ ensures true;
{
  //@ open table(_tbl, _, _);
  free(_tbl->tbl_24);
  free(_tbl->tbl_long);
  free(_tbl);
}

int tbl_update_elem(struct tbl *_tbl, struct key *_key)
//@ requires table(_tbl, ?long_index, ?dir) &*& key(_key, ?ipv4, ?plen, ?route);
/*@ ensures table(_tbl, long_index,
                  add_rule(dir,
                           init_rule(ipv4, plen, route)
                  )
            )
            &*& key(_key, ipv4, plen, route);
@*/
{
  //@ open key(_key, ipv4, plen, route);
  //@ open table(_tbl, long_index, dir);
  uint8_t prefixlen = _key->prefixlen;
  uint32_t data = _key->data;
  uint16_t value = _key->route;
  uint16_t *tbl_24 = _tbl->tbl_24;
  uint16_t *tbl_long = _tbl->tbl_long;

  if(prefixlen > TBL_PLEN_MAX || value > MAX_NEXT_HOP_VALUE){
    //@ close key(_key, ipv4, plen, route);
    //@ close table(_tbl, long_index, dir);
    return -1;
  }

  uint32_t masked_data = data & build_mask_from_prefixlen(prefixlen);

  //If prefixlen is smaller than 24, simply store the value in tbl_24
  if(prefixlen < 24){
    uint32_t first_index = tbl_24_extract_first_index(masked_data);
    uint32_t rule_size = compute_rule_size(prefixlen);
    uint32_t last_index = first_index + rule_size;

    //fill all entries between first index and last index with value
    for(uint32_t i = 0; i < TBL_24_MAX_ENTRIES; i++)
    //@ requires tbl_24[i..TBL_24_MAX_ENTRIES] |-> _;
    //@ ensures tbl_24[old_i..TBL_24_MAX_ENTRIES] |-> _;
    {
      if(i >= first_index && i < last_index){
	    tbl_24[i] = value;
      }
    }
    //@ close key(_key, ipv4, plen, route);
    //@ close table(_tbl, long_index, dir);
    } else {
    //If the prefixlen is not smaller than 24, we have to store the value
    //in tbl_long.

      //Check the tbl_24 entry corresponding to the key. If it already has a
      //flag set to 1, use the stored value as base index, otherwise get a new
      //index and store it in the tbl_24
      uint8_t base_index;
      uint32_t tbl_24_index = tbl_24_extract_first_index(data);
      
      uint16_t tbl_24_value = tbl_24[tbl_24_index];
      //@ close entry_24(entry_24_mapping(tbl_24_value));
      bool flag = tbl_24_entry_flag(tbl_24_value);
      bool need_new_index = !flag || tbl_24[tbl_24_index] == INVALID;
      
      if(need_new_index){
        if(_tbl->tbl_long_index >= TBL_LONG_OFFSET_MAX){

          printf("No more available index for tbl_long!\n");fflush(stdout);
          //@ close key(_key, ipv4, plen, route);
          //@ close table(_tbl, 256, dir);
          return -1;
		
        }else{
        //generate next index and store it in tbl_24
          base_index = (uint8_t)(_tbl->tbl_long_index);
          _tbl->tbl_long_index = (uint16_t)(base_index + 1);
            
          tbl_24[tbl_24_index] = tbl_24_entry_set_flag(base_index);
        }      
      }else{
        uint16_t tbl_24_value = tbl_24[tbl_24_index];
        base_index = (uint8_t)(tbl_24_value & 0xFF);
      }
      

      //The last byte in data is used as the starting offset for tbl_long
      //indexes
      uint32_t first_index = tbl_long_extract_first_index(data, prefixlen, base_index);
      uint32_t last_index = first_index + compute_rule_size(prefixlen);

      //Store value in tbl_long entries indexed from value*256+offset up to
      //value*256+255
      for(uint32_t i = 0; i < TBL_LONG_MAX_ENTRIES; i++)
      //@ requires tbl_long[i..TBL_LONG_MAX_ENTRIES] |-> _;
      //@ ensures tbl_long[old_i..TBL_LONG_MAX_ENTRIES] |-> _;
      {
        
        if(i >= first_index && i < last_index){
          tbl_long[i] = value;
        }
      }
      //@ close key(_key, ipv4, plen, route);
      //@ close table(_tbl, _, _);
    }
  return 0;
}

int tbl_lookup_elem(struct tbl *_tbl, uint32_t data)
//@ requires table(_tbl, ?long_index, ?dir);
//@ ensures table(_tbl, long_index, dir) &*& result == lpm_dir_24_8_lookup(Z_of_int(data, N32),dir);
{
  //@ open table(_tbl, long_index, dir);
  uint16_t *tbl_24 = _tbl->tbl_24;
  uint16_t *tbl_long = _tbl->tbl_long;

  //get index corresponding to key for tbl_24
  uint32_t index = tbl_24_extract_first_index(data);

  uint16_t value = tbl_24[index];
	
  if(value != INVALID && tbl_24_entry_flag(value)){
  //the value found in tbl_24 is a base index for an entry in tbl_long,
  //go look at the index corresponding to the key and this base index
    //@ bitand_limits(data, 0xFF, N32);
    uint32_t index_long = tbl_long_extract_first_index(data, (uint8_t)(value & 0xFF));
    uint16_t value_long = tbl_long[index_long];
    //@ close table(_tbl, long_index, dir);
    return value_long;
  } else {
  //the value found in tbl_24 is the next hop, just return it
    //@ close table(_tbl, long_index, dir);
    return value;
  }
}
