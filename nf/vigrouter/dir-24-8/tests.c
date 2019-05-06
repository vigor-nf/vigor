#include "dir-24-8-basic.h"
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stddef.h>
#include <assert.h>


struct key *allocate_key(uint32_t data, uint8_t prefixlen, uint16_t route)
{
    struct key *k = malloc(sizeof(struct key));
    if(k == 0){
        return NULL;
    }

    k->data = data;
    k->prefixlen = prefixlen;
    k->route = route;

    return k;
}

void mask_tests(){
	uint8_t prefixlen = 0;
	uint32_t res = build_mask_from_prefixlen(prefixlen);
	assert(res == 0);
	
	prefixlen = 32;
	res = build_mask_from_prefixlen(prefixlen);
	assert(res == 0xFFFFFFFF);
	
	prefixlen = 17;
	res = build_mask_from_prefixlen(prefixlen);
	assert(res == 0xFFFF8000);
	
	res = tbl_24_extract_first_index(0xFFFFFFFF);
	assert(res == 0xFFFFFF);
	
	res = compute_rule_size(0);
	assert(res == 0x1000000);
	
	res = compute_rule_size(32);
	assert(res == 1);
	
	res = tbl_24_entry_set_flag(0);
	assert(res == 0x8000);
	
	res = tbl_long_extract_first_index(0x12345678, 32, 43);
	assert(res == 43*256+0x78);
	
	printf("mask_tests OK!\n");fflush(stdout);
	
}

void t24_then_26_mask_rules_test(){
	struct tbl *table = tbl_allocate(TBL_24_MAX_ENTRIES);
	if(table == 0){abort();}
	
	uint32_t data = 0xC0A80544;
	//Add a general rule
	struct key* k = allocate_key(data, 24, 53);
	tbl_update_elem(table, k);

	//Test with min index
	uint32_t min_24 = 0xC0A80500;
	int res = tbl_lookup_elem(table, min_24);
	assert(res == 53);
	
	//Test with max index
	uint32_t max_24 = 0xC0A805FF;
	res = tbl_lookup_elem(table, max_24);
	assert(res == 53);
	
	//Now we add a more precise rule
	free(k);
	k = allocate_key(data, 26, 36);
	tbl_update_elem(table, k);
	
	//Test with min index
	uint32_t min_26 = 0xC0A80540;
	res = tbl_lookup_elem(table, min_26);
	assert(res == 36);
	
	//Test with max index
	uint32_t max_26 = 0xC0A8057F;
	res = tbl_lookup_elem(table, max_26);
	assert(res == 36);
	
	//Min and max of mask 24 should not have been touched
	res = tbl_lookup_elem(table, min_24);
	assert(res == 53);
	res = tbl_lookup_elem(table, max_24);
	assert(res == 53);
	
	tbl_free(table);
	free(k);
	
	printf("t24_then_26_mask_rules_test OK!\n");fflush(stdout);
}

int main()
{
	mask_tests();
	t24_then_26_mask_rules_test();
}
