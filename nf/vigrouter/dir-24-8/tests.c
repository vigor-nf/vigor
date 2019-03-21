#include "dir-24-8-basic.h"
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stddef.h>
#include <assert.h>


struct key *allocate_key(uint8_t *data, uint8_t prefixlen)
{
    struct key *key = (struct key *) malloc(sizeof(struct key));
    if(!key){
        return NULL;
    }

    memcpy(key->data, data, 4);
    key->prefixlen = prefixlen;

    return key;
}

int unit_tests(){
	
	struct tbl *table = tbl_allocate(TBL_24_MAX_ENTRIES);
	if(table == 0){abort();}

	uint8_t data[4] = {128,23,5,75};
	struct key *k1 = allocate_key(data, 16);

	tbl_update_elem(table, k1, 3);
	
	uint8_t data2[4] = {128,23,0,0};
	int res = tbl_lookup_elem(table, data2);
	assert(res == 3);
	printf("128.23.0.0 -> %d\n", res);
	
	uint8_t data3[4] = {129,23,5,75};
	struct key *k2 = allocate_key(data3, 26);
	
	tbl_update_elem(table, k2, 53);
	res = tbl_lookup_elem(table, data3);
	assert(res == 53);
	printf("129.23.5.75 -> %d\n", res);
	
	//test with min index
	uint8_t data4[4] = {129,23,5,64};
	res = tbl_lookup_elem(table, data4);
	assert(res == 53);
	printf("129.23.5.64 -> %d\n", res);
	
	//test with max index
	uint8_t data5[4] = {129,23,5,127};
	res = tbl_lookup_elem(table, data5);
	assert(res == 53);
	printf("129.23.5.12 -> %d\n", res);
	
	//Now put a smaller mask
	uint8_t data6[4] = {129,23,5,150};
	struct key* k3 = allocate_key(data6, 24);
	
	tbl_update_elem(table, k3, 36);
	
	//test with min index
	uint8_t data7[4] = {129,23,5,0};
	res = tbl_lookup_elem(table, data7);
	assert(res == 36);
	printf("129.23.5.0 -> %d\n", res);
	
	//test with max index
	uint8_t data8[4] = {129,23,5,255};
	res = tbl_lookup_elem(table, data8);
	assert(res == 36);
	printf("129.23.5.255 -> %d\n", res);
	
	//previous entry (data3) should still be at 53 since the rule was more precise
	res = tbl_lookup_elem(table, data3);
	printf("\nresult of lookup is %d\n",res);
	assert(res == 53);
	printf("129.23.5.75 -> %d\n", res);
	
	tbl_free(table);
	free(k1);
	free(k2);
	free(k3);
	
	return 0;
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
	
	printf("mask_tests OK!\n");
	
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
	
	printf("t24_then_26_mask_rules_test OK!\n");
}

void linked_list_test(){
	struct entry *_entry = malloc(sizeof(struct entry));
	
	linked_list_insertion(_entry, 16, 4);
	linked_list_insertion(_entry, 26, 1);
	linked_list_insertion(_entry, 23, 2);
	
	assert(_entry->current_rule->value == 1);
	assert(_entry->current_rule->next->value == 2);
	assert(_entry->current_rule->next->next->value == 4);
	assert(_entry->current_rule->next->next->next == 0);
	
	linked_list_deletion(_entry, 26);
	assert(_entry->current_rule->value == 2);
	assert(_entry->current_rule->next->value == 4);
	assert(_entry->current_rule->next->next == 0);
	
	linked_list_insertion(_entry, 3, 5);
	assert(_entry->current_rule->value == 2);
	assert(_entry->current_rule->next->value == 4);
	assert(_entry->current_rule->next->next->value == 5);
	assert(_entry->current_rule->next->next->next == 0);
	
	free_rules(_entry->current_rule);
	free(_entry);
	
	printf("linked_list_test OK!\n");
}

void bitmap_test(){
	struct bitmap* bmap = create_bitmap(256);
	
	assert(bmap->size == 256);
	
	//Verify everything is 0
	for(size_t i = 0; i < 256; i++){
		assert(0 == bmap->map[i]);
	}
	
	for(size_t i = 0; i < 256; i++){
		size_t index = take_first_free_index(bmap);
		//printf("%d %d\n",i, index);fflush(stdout);
		assert(i == index);
	}
	
	assert(is_bitmap_full(bmap));
	
	assert(bmap->size == take_first_free_index(bmap));
	
	//free an outbounded index
	free_bitmap_index(bmap, 300);
	assert(is_bitmap_full(bmap));
	
	//free valid indexes and take them back
	free_bitmap_index(bmap, 36);
	free_bitmap_index(bmap, 18);
	assert(18 == take_first_free_index(bmap));
	assert(36 == take_first_free_index(bmap));
	
	free_bitmap(bmap);
	
	printf("Bitmap OK !\n");
}


int main()
{
	linked_list_test();
	mask_tests();
	bitmap_test();
	t24_then_26_mask_rules_test();
	unit_tests();
}
