#include "dir-24-8-basic.h"
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stddef.h>
#include <assert.h>


struct key *allocate_key(uint8_t *data, uint8_t prefixlen)
{
    struct key *k = malloc(sizeof(struct key));
    if(k == 0){
        return NULL;
    }

    memcpy(k->data, data, 4);
    k->prefixlen = prefixlen;

    return k;
}

void mask_tests(){
	uint8_t prefixlen = 0;
	size_t res = build_mask_from_prefixlen(prefixlen);
	assert(res == 0);
	
	prefixlen = 32;
	res = build_mask_from_prefixlen(prefixlen);
	assert(res == 0xFFFFFFFF);
	
	prefixlen = 17;
	res = build_mask_from_prefixlen(prefixlen);
	assert(res == 0xFFFF8000);
	
	printf("mask_tests OK!\n");fflush(stdout);
	
}

void t24_then_26_mask_rules_test(){
	struct tbl *table = tbl_allocate(TBL_24_MAX_ENTRIES);
	if(table == 0){abort();}
	
	uint8_t data[4] = {192,168,5,68};
	//Add a general rule
	struct key* k = allocate_key(data, 24);
	tbl_update_elem(table, k, 53);

	//Test with min index
	uint8_t min_24[4] = {192,168,5,0};
	int res = tbl_lookup_elem(table, min_24);
	assert(res == 53);
	
	//Test with max index
	uint8_t max_24[4] = {192,168,5,255};
	res = tbl_lookup_elem(table, max_24);
	assert(res == 53);
	
	//Now we add a more precise rule
	free(k);
	k = allocate_key(data, 26);
	tbl_update_elem(table, k, 36);
	
	//Test with min index
	uint8_t min_26[4] = {192,168,5,64};
	res = tbl_lookup_elem(table, min_26);
	assert(res == 36);
	
	//Test with max index
	uint8_t max_26[4] = {192,168,5,127};
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
