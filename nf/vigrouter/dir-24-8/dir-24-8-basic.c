#include "dir-24-8-basic.h"
//@ #include <nat.gh>
//@ #include <bitops.gh>
// #include lpm_dir_24_8.gh'

size_t build_mask_from_prefixlen(uint8_t prefixlen)
    //@ requires prefixlen <= 32;
    //@ ensures true;
{
	if(prefixlen > 32){abort();}
	uint32_t mask = 0;
	
	
	for(int i = 0; ;i++)
	//@ invariant 0 <= i &*& i <= prefixlen;// &*& mask == (pow_nat(2, nat_of_int(i))-1);
	{
		if(i == prefixlen){
			break;
		}
		// shiftleft_def(mask, nat_of_int(1));
		// shiftleft_limits(mask, nat_of_int(31), nat_of_int(1));
		mask <<= 1;
		// bitor_limits(mask, 1, nat_of_int(32));
		mask |= 1;
		
	}
	
	// shiftleft_limits(mask, nat_of_int(prefixlen), nat_of_int(32 - prefixlen));
	mask <<= (32 - prefixlen);
	
	return mask;
}

size_t shift_left_eight(uint32_t x)
    //@ requires true;
    //@ ensures true;
{
    //size_t res = x;
    
    //res = res << 8;
    // shiftleft_limits(x, nat_of_int(32), nat_of_int(8));
    return x << 8;
}

size_t uint_or(size_t x, size_t y)
    //@ requires true;
    //@ ensures true;
{
    // bitor_limits(x, y, nat_of_int(32));
    size_t res = x | y;
    return res;
}


/**
 * Extract the 24 MSB of an uint8_t array and returns then in size_t
 */
size_t tbl_24_extract_first_index(uint8_t *data)
    //@ requires data[0..4] |-> ?ipv4;
    //@ ensures data[0..4] |-> ipv4;
{
    size_t index = 0;
    
    index = uint_or(index, (size_t)data[0]);
    
    index = shift_left_eight(index);
    
    index = uint_or(index, (size_t)data[1]);
    
    index = shift_left_eight(index);
    
    index = uint_or(index, (size_t)data[2]);
    
    return index;
}

/**
 * Apply a mask of prefixlen to a 32bits address that had been cut to the 24 MSB 
 */
size_t correct_first_index_with_mask(size_t first_index, uint8_t prefixlen)
{
	//No need for a mask
	if(prefixlen >= 24){
	    return first_index;
	}
	
	size_t mask = build_mask_from_prefixlen(prefixlen);
	
	return (first_index & (mask >> 8));
}

/**
 * Computes the last index reached by the IP/mask pair contained in key
 */
size_t tbl_24_extract_last_index(struct key *key)
    // requires key(key, ?ipv4);
    // ensures key(key, ipv4);
{
    //Auto open
    uint8_t *data = key->data;
    size_t prefixlen = key->prefixlen;

    size_t index = tbl_24_extract_first_index(data);

    if(prefixlen < TBL_24_PLEN_MAX){
        size_t fill = 1;
        for(int i = 1; i < TBL_24_PLEN_MAX - prefixlen; i++){
            fill <<= 1;
            fill |= 1;
        }
        index |= fill;
    }

    return index;
}

uint8_t *tbl_24_make_data_from_index(size_t index)
{
    uint8_t* data = calloc(4, sizeof(uint8_t));
    if(data == 0){abort();}
    
    data[0] = index >> 16;
    data[1] = (index << 8) >> 16;
    data[2] = (index << 16) >> 16;
    data[3] = 0;
    
    return data;
}

int tbl_24_entry_flag(uint16_t _entry)
{
    uint16_t res = _entry >> 15;
    return (int)res;
}

uint16_t tbl_24_entry_set_flag(uint16_t _entry)
{
    return _entry | TBL_24_FLAG_MASK;
}

size_t tbl_long_extract_first_index(uint8_t *data, size_t base_index)
{
    return base_index * TBL_LONG_FACTOR + data[3];
}

size_t tbl_long_extract_last_index(struct key *key, size_t base_index)
{
    uint8_t offset = key->data[3];
    size_t prefixlen = key->prefixlen;

    size_t fill = 1;
    for(int i = 1; i < TBL_PLEN_MAX - prefixlen; i++){
        fill <<= 1;
        fill |= 1;
    }
    offset |= fill;

    return base_index * TBL_LONG_FACTOR + offset;
}

/*@
fixpoint bool is_zero(uint16_t x){
    return x == 0 ? true : false;
}
@*/

//Is it useful to let a max_entries param??
struct tbl *tbl_allocate(size_t max_entries)
    //@ requires true;
    /*@ ensures result == 0 ? true : table(result, ?tbl_24, ?tbl_long);
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
    memset(tbl_24, 0, TBL_24_MAX_ENTRIES);
    memset(tbl_long, 0, TBL_LONG_MAX_ENTRIES);
        
    _tbl->tbl_24 = tbl_24;
    _tbl->tbl_long = tbl_long;
    _tbl->tbl_long_index = 0;
    _tbl->n_entries = 0;
    _tbl->max_entries = max_entries;

    return _tbl;
}


void tbl_free(struct tbl *_tbl)
    //@ requires table(tbl, _, _);
    //@ ensures true;
{
    free(_tbl->tbl_24);
    free(_tbl->tbl_long);
    free(_tbl);
}

int tbl_update_elem(struct tbl *_tbl, struct key *_key, uint8_t value)
{
    if(!_tbl || !_key){
        return -1;
    }

    uint8_t prefixlen = _key->prefixlen;
    uint8_t *data = _key->data;
    uint16_t *tbl_24 = _tbl->tbl_24;
    uint16_t *tbl_long = _tbl->tbl_long;

    if(!tbl_24 || !tbl_long || !data || prefixlen > TBL_PLEN_MAX ||
        _tbl->n_entries >= _tbl->max_entries || value > MAX_NEXT_HOP_VALUE){
        return -1;
    }

    _tbl->n_entries ++;

    //If prefixlen is smaller than 24, simply store the value in tbl_24, in
    //entries indexed from data[0].data[1].data[2] up to data[0].data[1].255
    if(prefixlen < 24){
        size_t first_index = tbl_24_extract_first_index(data);
        //Simon: Apply subnet mask
        first_index = correct_first_index_with_mask(first_index, prefixlen);
        size_t last_index = tbl_24_extract_last_index(_key);

        //fill all entries between first index and last index with value
        for(int i = first_index; i <= last_index; i++){
			tbl_24[i] = value;
        }
    } else {
        //If the prefixlen is not smaller than 24, we have to store the value
        //in tbl_long.

        //Check the tbl_24 entry corresponding to the key. If it already has a
        //flag set to 1, use the stored value as base index, otherwise get a new
        //index and store it in the tbl_24
        size_t base_index;
        size_t tbl_24_index = tbl_24_extract_first_index(data);
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
        
        //Simon: Apply the subnet mask to the last byte
        data[3] = data[3] & (build_mask_from_prefixlen(prefixlen) & 0xFF);
        
        size_t first_index = tbl_long_extract_first_index(data, base_index);
        size_t last_index = tbl_long_extract_last_index(_key, base_index);

        //Store value in tbl_long entries indexed from value*256+offset up to
        //value*256+255
        for(int i = first_index; i <= last_index; i++){
			tbl_long[i] = value;
        }
    }

    return 0;
}

int tbl_lookup_elem(struct tbl *_tbl, uint8_t* data)
{
    if(!_tbl || !data){
        return -1;
    }

    uint16_t *tbl_24 = _tbl->tbl_24;
    uint16_t *tbl_long = _tbl->tbl_long;

    if(!tbl_24 || !tbl_long || !data){
        return -1;
    }

    //get index corresponding to key for tbl_24
    size_t index = tbl_24_extract_first_index(data);
    uint16_t value = tbl_24[index];
	
	if(tbl_24_entry_flag(value)){
        //the value found in tbl_24 is a base index for an entry in tbl_long,
        //go look at the index corresponding to the key and this base index
        size_t index_long = tbl_long_extract_first_index(data, value & TBL_24_VAL_MASK);
        uint16_t value_long = tbl_long[index_long];
        return value_long;
    } else {
        //the value found in tbl_24 is the next hop, just return it
        return value;
    }
}
