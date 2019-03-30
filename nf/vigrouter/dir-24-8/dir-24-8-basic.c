#include "dir-24-8-basic.h"
//@ #include <nat.gh>
//@ #include <bitops.gh>

/*@
fixpoint bool is_zero(uint16_t x){
    return x == 0;
}

fixpoint uint16_t map_zero(uint16_t x){
    return 0;
}
@*/

void fill_zeros(uint16_t *t, uint32_t size)
    //@ requires t[0..size] |-> _;
    //@ ensures t[0.. size] |-> ?entries &*& true == forall(entries, is_zero);
{
    for(uint32_t i = 0; i < size; i++)
    //@ invariant;
    {
    	t[i] = 0;
    }
}

uint32_t build_mask_from_prefixlen(uint8_t prefixlen)
    //@ requires prefixlen <= 32;
    //@ ensures true;
{
	if(prefixlen > 32){abort();}
	size_t mask = 0xFFFFFFFF;
	
	mask = mask >> (32-prefixlen);
	mask = mask << (32-prefixlen);
	
	return (uint32_t)mask;
}

/*@
lemma void bounded_uint8(uint8_t x);
    requires true;
    ensures 0 <= x &*& x <= 0xFF;
   
lemma void identity_shift(uint32_t x);
    requires x <= 0xFFFFFF;
    ensures x == ((x << 8) >> 8);
 
@*/
/* @
fixpoint uint32_t extract_index_24(list<uint8_t> ipv4, uint32_t acc){
    switch(ipv4){
    	case nil: return acc >> 8;
    	case cons(v, cs0): return acc <= 0xFFFFFF ? extract_index_24(cs0, (acc | v) << 8) : 0;
    }
}
@*/

/**
 * Extract the 24 MSB of an uint8_t array and returns then in size_t
 */
uint32_t tbl_24_extract_first_index(uint32_t data)
    //@ requires data[0..4] |-> ?ipv4;
    //@ ensures data[0..4] |-> ipv4;// &*& result == extract_index_24(ipv4, 0);
{
    uint32_t index = data >> BYTE_SIZE;
    
    return index;
}


/**
 * Computes how many entries the rule will take
 */
uint32_t compute_rule_size(uint8_t prefixlen)
{	
	uint32_t res = prefixlen < 24 ? 1 << (24 - prefixlen) : 1 << (32 - prefixlen);
	
	return res;
}

bool tbl_24_entry_flag(uint16_t _entry)
    //@ requires true;
    //@ ensures result == (_entry >> 15 == 1);
{
    return (_entry >> 15) == 1;
}

uint16_t tbl_24_entry_set_flag(uint16_t _entry)
    //@ requires true;
    //@ ensures result == (_entry | TBL_24_FLAG_MASK);
{
    //@ bitor_limits(_entry, TBL_24_FLAG_MASK, nat_of_int(16));
    return (uint16_t)(_entry | TBL_24_FLAG_MASK);
}

/*@
fixpoint uint16_t compute_long_index(list<uint8_t> ipv4, uint8_t base_index){
    return base_index * TBL_LONG_FACTOR + nth(3, ipv4);
}
@*/
uint16_t tbl_long_extract_first_index(uint32_t data, uint8_t base_index)
    //@ requires data[0..4] |-> ?ipv4;
    //@ ensures data[0..4] |-> ipv4 &*& result == compute_long_index(ipv4, base_index);
{
    //@ bounded_uint8(base_index);
    //@ bounded_uint8(nth(3, ipv4));
    
    uint32_t last_byte = data & 0xFF;
    
    return (uint16_t)(base_index * TBL_LONG_FACTOR + last_byte);
}

struct tbl *tbl_allocate()
    //@ requires true;
    /*@ ensures result == 0 ? true : (table(result, ?tbl_24, ?tbl_long) &*& forall(tbl_24, is_zero) == true &*& forall(tbl_long, is_zero) == true);
    @*/
{	
    struct tbl *_tbl = malloc(sizeof(struct tbl));
    if(_tbl == 0){
    	return 0;
    }
    
    uint16_t *tbl_24 = (uint16_t *) malloc(TBL_24_MAX_ENTRIES * sizeof(uint16_t)); //array of pointers on structs
    if(tbl_24 == 0){
        free(_tbl);
        return 0;
    }
    
    uint16_t *tbl_long = (uint16_t *) malloc(TBL_LONG_MAX_ENTRIES * sizeof(uint16_t));
    if(tbl_long == 0){
        free(tbl_24);
        free(_tbl);
        return 0;
    }
    //Set every element of the array to zero
    fill_zeros(tbl_24, TBL_24_MAX_ENTRIES);
    fill_zeros(tbl_long, TBL_LONG_MAX_ENTRIES);
        
    _tbl->tbl_24 = tbl_24;
    _tbl->tbl_long = tbl_long;
    _tbl->tbl_long_index = 0;
    _tbl->n_entries = 0;

    return _tbl;
}


void tbl_free(struct tbl *_tbl)
    //@ requires table(_tbl, _, _);
    //@ ensures true;
{
    free(_tbl->tbl_24);
    free(_tbl->tbl_long);
    free(_tbl);
}

int tbl_update_elem(struct tbl *_tbl, struct key *_key)
    //@ requires table(_tbl, ?t_24, ?t_l) &*& key(_key, ?ipv4);
    //@ ensures table(_tbl, t_24, t_l) &*& key(_key, ipv4);
{
    uint8_t prefixlen = _key->prefixlen;
    uint32_t data = _key->data;
    uint16_t value = _key->route;
    uint16_t *tbl_24 = _tbl->tbl_24;
    uint16_t *tbl_long = _tbl->tbl_long;

    if(prefixlen > TBL_PLEN_MAX || value > MAX_NEXT_HOP_VALUE){
        return -1;
    }

	uint32_t masked_data = data & build_mask_from_prefixlen(prefixlen);

    //If prefixlen is smaller than 24, simply store the value in tbl_24, in
    //entries indexed from data[0].data[1].data[2] up to data[0].data[1].255
    if(prefixlen < 24){
        uint32_t first_index = masked_data;
        uint32_t last_index = first_index + compute_rule_size(prefixlen);

        //fill all entries between first index and last index with value
        for(int i = first_index; i < last_index; i++){
		tbl_24[i] = value;
		_tbl->n_entries++;
        }
    } else {
        //If the prefixlen is not smaller than 24, we have to store the value
        //in tbl_long.

        //Check the tbl_24 entry corresponding to the key. If it already has a
        //flag set to 1, use the stored value as base index, otherwise get a new
        //index and store it in the tbl_24
        uint8_t base_index;
        uint32_t tbl_24_index = tbl_24_extract_first_index(data);
        
        if(tbl_24[tbl_24_index] == 0){
            _tbl->n_entries++;
        }
        
        if(tbl_24_entry_flag(tbl_24[tbl_24_index])){
            base_index = tbl_24[tbl_24_index] & TBL_24_VAL_MASK;
        } else {
			if(_tbl->tbl_long_index == TBL_LONG_OFFSET_MAX){
				printf("No more available index for tbl_long!\n");fflush(stdout);
				return -1;
			}
            //generate next index and store it in tbl_24
            base_index = _tbl->tbl_long_index + 1;
            _tbl->tbl_long_index = base_index;
            
            tbl_24[tbl_24_index] = tbl_24_entry_set_flag(base_index);
        }

        //The last byte in data is used as the starting offset for tbl_long
        //indexes
        uint32_t first_index = tbl_long_extract_first_index(masked_data, base_index);
        uint32_t last_index = first_index + compute_rule_size(prefixlen);

        //Store value in tbl_long entries indexed from value*256+offset up to
        //value*256+255
        for(int i = first_index; i < last_index; i++){
			tbl_long[i] = value;
        }
    }

    return 0;
}

int tbl_lookup_elem(struct tbl *_tbl, uint32_t data)
    //@ requires table(_tbl, ?t_24, ?t_l);
    //@ ensures table(_tbl, t_24, t_l);
{
    uint16_t *tbl_24 = _tbl->tbl_24;
    uint16_t *tbl_long = _tbl->tbl_long;

    //get index corresponding to key for tbl_24
    uint32_t index = tbl_24_extract_first_index(data);
    uint16_t value = tbl_24[index];
	
	if(tbl_24_entry_flag(value)){
        //the value found in tbl_24 is a base index for an entry in tbl_long,
        //go look at the index corresponding to the key and this base index
        uint32_t index_long = tbl_long_extract_first_index(data, value & TBL_24_VAL_MASK);
        uint16_t value_long = tbl_long[index_long];
        return value_long;
    } else {
        //the value found in tbl_24 is the next hop, just return it
        return value;
    }
}
