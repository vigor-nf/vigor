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


uint8_t *tbl_24_is_last_index(size_t index, struct tbl *_tbl)
{
    struct entry **tbl_24 = _tbl->tbl_24;
    size_t prefixlen = tbl_24[index]->prefixlen;

    size_t mask = 1;
    for(int i = 1; i < TBL_24_PLEN_MAX - prefixlen; i++){
        mask <<= 1;
        mask |= 1;
    }

    size_t res = index & mask;//Has to be only ones
    if(res == (2 << (TBL_24_PLEN_MAX - prefixlen)) - 1){
        return tbl_24_make_data_from_index(index);
    } else {
        return 0;
    }
}

int tbl_24_entry_flag(uint16_t _entry)
{
    uint16_t res = (_entry & TBL_24_FLAG_MASK) >> 15;
    return (int)res;
}

/*struct entry* tbl_24_find_replacement(struct key *_key, struct tbl *_tbl)
{
    if(_key->prefixlen < 1)
        return 0;

    struct entry **tbl_24 = _tbl->tbl_24;
    uint8_t *data = _key->data;

    size_t first = tbl_24_extract_first_index(data);
    size_t current = first - 1;
    uint8_t *current_data;

    while(current >= 0 &&
            ((current_data = tbl_24_is_last_index(current, _tbl)) ||
                tbl_24_entry_flag(tbl_24[current]->value))){

        if(tbl_24_is_last_index(current, _tbl)){
            current = tbl_24_extract_first_index(current_data) - 1;
        } else if(tbl_24_entry_flag(tbl_24[current]->value)){
            current --;
        }
    }

    if(current < 0){
        return 0;
    }

    return tbl_24[current];
}*/

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


uint8_t *tbl_long_is_last_index(size_t index, struct tbl *_tbl,
                                size_t base_index)
{
    struct entry **tbl_long = _tbl->tbl_long;
    size_t prefixlen = tbl_long[index]->prefixlen;

    size_t mask = 1;
    for(int i = 1; i < TBL_PLEN_MAX - prefixlen; i++){
        mask <<= 1;
        mask |= 1;
    }

    size_t res = index & mask;//Has to be only ones
    if(res == (2 << (TBL_PLEN_MAX - prefixlen)) - 1){
        return tbl_24_make_data_from_index(index);
    } else {
        return NULL;
    }
}

uint16_t tbl_long_find_replacement(struct key *_key, struct tbl *_tbl,
                                    size_t base_index)
{
    if(_key->prefixlen < 25)
        return 0;

    struct entry **tbl_long = _tbl->tbl_long;
    uint8_t *data = _key->data;

    uint8_t *current_data;
    size_t current = tbl_long_extract_first_index(data, base_index) -1;
    while(current >= base_index * TBL_LONG_FACTOR &&
            (current_data = tbl_long_is_last_index(current, _tbl, base_index))){
                current =
                    tbl_long_extract_first_index(current_data, base_index) - 1;
            }

    if(current < base_index * TBL_LONG_FACTOR){
        return 0;
    } else {
        return tbl_long[current];
    }
}

/*@
fixpoint bool is_zero(uint16_t x){
    return x == 0 ? true : false;
}
@*/

void fill_with_zeros(struct entry** array, size_t size)
    // requires array[0..size] |-> ?data;
    // ensures true == forall(data, is_zero) &*& array[0..size] |-> data;
{
    
    for(int i = 0; ; i++)
    // requires array[0..i] |-> ?zeros &*& array[i..size] |-> ?whatever &*& true == forall(zeros, is_zero);
    // ensures array[0..old_i] |-> zeros &*& array[old_i..size] |-> whatever &*& true == forall(zeros, is_zero);
    {
        if(i == size){
            break;
        }
        
        array[i]->current_rule = 0;
    }
}

//Is it useful to let a max_entries param??
struct tbl *tbl_allocate(size_t max_entries)
    //@ requires true;
    /*@ ensures result == 0 ? true : table(result, ?tbl_24, ?tbl_long);
    @*/
{
    struct tbl *_tbl = malloc(sizeof(struct tbl));
    if(!tbl){
    	abort();
    }

    size_t tbl_24_size = TBL_24_MAX_ENTRIES * sizeof(struct entry);
    struct entry **tbl_24 = (struct entry **) malloc(tbl_24_size); //array of pointers on structs
    if(!tbl_24){
        free(_tbl);
        return 0;
    }
    
    size_t tbl_long_size = TBL_LONG_MAX_ENTRIES * sizeof(struct entry);
    struct entry **tbl_long = (struct entry **) malloc(tbl_long_size);
    if(!tbl_long){
        free(tbl_24);
        free(_tbl);
        return 0;
    }
    
    //Set every element of the array to zero
    fill_with_zeros(tbl_24, TBL_24_MAX_ENTRIES);
    fill_with_zeros(tbl_long, TBL_LONG_MAX_ENTRIES);


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
	//MUST FREE THE RULES
    free(_tbl->tbl_24);
    free(_tbl->tbl_long);
    free(_tbl);
}

/**
 * Inserts a new rule in the linked list, no duplicate, rule with the longer prefixlen is at head
 * if same prefixlen->update value
 */
void linked_list_insertion(struct entry* _entry, uint8_t prefixlen, uint16_t value)
{
	struct rule* new_rule = malloc(sizeof(struct rule));
	if(rule == 0){abort();}
	
	new_rule->prefixlen = prefixlen;
	new_rule->value = value;
	new_rule->next = 0;
	
	if(_entry->current_rule == 0){
		//New rule is head
		_entry->current_rule = new_rule;
	}else{
		struct rule* current = _entry->current_rule;
		
		while(current->next != 0 && current->prefixlen > prefixlen){
			current = current->next;
		}
		
		if(current->prefixlen == prefixlen){
			//If same prefixlen, just update the value
			current->value = value;
			free(new_rule);
		}else{
			//Add the new rule
			new_rule->next = current->next;
			current->next = new_rule;
		}
	}
}

/**
 * Deletes a rule in the linked list
 */
void linked_list_deletion(struct entry* _entry, uint8_t prefixlen){
	
	if(_entry->current_rule = 0){
		//List is empty, nothing to do
	}else{
		struct rule* previous = 0;
		struct rule* current = _entry->current_rule;
		
		//Lazy evaluation on the second condition
		while(current != 0 && current->prefixlen != prefixlen){
			previous = current;
			current = current->next;
		}
		
		if(current == 0){
			//Rule not found, nothing to do
		}else{
			if(previous == 0){
				//Current is head, next becomes head
				_entry->current_rule = current->next;
			}else{
				previous->next = current->next;
			}
			free(current);
		}
		
	}
}

int tbl_update_elem(struct tbl *_tbl, struct key *_key, uint8_t value)
{
    if(!_tbl || !_key){
        return -1;
    }

    uint8_t prefixlen = _key->prefixlen;
    uint8_t *data = _key->data;
    struct entry **tbl_24 = _tbl->tbl_24;
    struct entry **tbl_long = _tbl->tbl_long;

    if(!tbl_24 || !tbl_long || !data || prefixlen > TBL_PLEN_MAX ||
        _tbl->n_entries >= _tbl->max_entries){
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

        //fill all entries between first index and last index with value if
        //these entries don't have a longer prefix associated with them
        for(int i = first_index; i <= last_index; i++){
			linked_list_insertion(tbl_24[i], prefixlen, value);
        }
    } else {
//CONTINUE FROM HERE
        //If the prefixlen is not smaller than 24, we have to store the value
        //in tbl_long.

        //Check the tbl_24 entry corresponding to the key. If it already has a
        //flag set to 1, use the stored value as base index, otherwise get a new
        //index and store it in the tbl_24
        size_t base_index;
        size_t tbl_24_index = tbl_24_extract_first_index(data);
        if(tbl_24_entry_flag(tbl_24[tbl_24_index]->value)){
            base_index = tbl_24_entry_val(tbl_24[tbl_24_index]->value);
        } else {
            //generate next index and store it in tbl_24
            base_index = _tbl->tbl_long_index;
            _tbl->tbl_long_index ++;
            tbl_24[tbl_24_index] = base_index;
            tbl_24[tbl_24_index] = tbl_24_entry_set_flag(tbl_24[tbl_24_index]);
            //record the prefix length associated with the entry
            tbl_24[tbl_24_index] = tbl_24_entry_put_plen(tbl_24[tbl_24_index],
                                                            prefixlen);
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
            if(tbl_long_entry_plen(tbl_long[i]) <= prefixlen){
                tbl_long[i] = value;
                //record length of the prefix associated with the entry
                tbl_long[i] = tbl_long_entry_put_plen(tbl_long[i], prefixlen);
            }
        }
    }

    return 0;
}

int tbl_delete_elem(struct tbl *_tbl, struct key *_key)
{
    if(!_tbl || !_key){
        return -1;
    }

    uint8_t prefixlen = _key->prefixlen;
    uint8_t *data = _key->data;
    uint16_t *tbl_24 = _tbl->tbl_24;
    uint16_t *tbl_long = _tbl->tbl_long;

    if(!tbl_24 || !tbl_long || !data || prefixlen > TBL_PLEN_MAX){
        return -1;
    }

    size_t tbl_24_index = tbl_24_extract_first_index(data);

    if(tbl_24_entry_flag(tbl_24[tbl_24_index]->value)) {
        //tbl_24 contains a base index for tbl_long
        size_t base_index = tbl_24_entry_val(tbl_24[tbl_24_index]->value);

        //remove all entries in tbl_long that match the key in argument and have
        //the same prefix length as the key in argument
        uint16_t replacement = tbl_long_find_replacement(_key, _tbl, base_index);

        size_t first_index = tbl_long_extract_first_index(data, base_index);
        size_t last_index = tbl_long_extract_last_index(_key, base_index);

        for(int i = first_index; i <= last_index; i++){
            if(tbl_long_entry_plen(tbl_long[i]) == prefixlen){
                tbl_long[i] = replacement;
            }
        }

        //then, remove the entry from tbl_24
        if(replacement != 0){
            size_t rep_plen = tbl_long_entry_plen(replacement);
            tbl_24[tbl_24_index] = tbl_24_entry_put_plen(tbl_24[tbl_24_index],
                                                            rep_plen);
        } else {
            tbl_24[tbl_24_index] = 0;
        }
    } else {
        //tbl_24 contains the next hop, just remove entries from the tbl_24 that
        //match the key given in argument and have the same prefix lentgh as the
        //key in argument

        uint16_t replacement = tbl_24_find_replacement(_key, _tbl);

        for(int i = tbl_24_extract_first_index(data);
            i <= tbl_24_extract_last_index(_key); i++){
            if(tbl_24[i]->prefixlen == prefixlen){
                tbl_24[i] = replacement;
            }
        }
    }

    _tbl->n_entries --;
    return 0;
}


int tbl_lookup_elem(struct tbl *_tbl, uint8_t* data)
{
    if(!_tbl || !data){
        return -1;
    }

    struct entry **tbl_24 = _tbl->tbl_24;
    struct entry **tbl_long = _tbl->tbl_long;

    if(!tbl_24 || !tbl_long || !data){
        return -1;
    }

    //get index corresponding to key for tbl_24
    size_t index = tbl_24_extract_first_index(data);

    struct entry *_entry = tbl_24[index];
    
    if(_entry->current_rule == 0){
		//No rule for the prefix
		return -1;
	}
	
	uint16_t tbl_24_entry_value = _entry->current_rule->value;
	
	if(tbl_24_entry_flag(tbl_24_entry_value)){
        //the value found in tbl_24 is a base index for an entry in tbl_long,
        //go look at the index corresponding to the key and this base index
        size_t index_long = tbl_long_extract_first_index(data, tbl_24_entry_value);
        return tbl_long_entry_val(tbl_long[index_long]->value);
    } else {
        //the value found in tbl_24 is the next hop, just return it
        return tbl_24_entry_value;
    }
}

