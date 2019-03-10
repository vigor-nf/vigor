
#include <assert.h>
#include "router.h"



void test_math();
void test_parse_utils();
void test_insert_in_trie();
void test_lookup();
int test_update_elem();

int main(){
	
	//test math_utils.c
	//testMath();			we don't use it anymore
	
	
	//test parse_utils.c
	
	test_parse_utils();
	
	//test the lookup
	test_lookup();
	
	
	//test trie initialization
	test_insert_in_trie();
	
	
	return 0;
}


void test_math(){
	
	//test math_utils.c/fast_exp
	int res = fast_exp(2,10);
	int res2 = fast_exp(2,0);
	
	assert(res == 1024);
	assert(res2 == 1);
}


void test_parse_utils(){
	
	
	//test parse_utils.c/get_number
	const char * s = "234";
	const char * s2 = "255";
	
	uint8_t ip_part = get_number(s,3);
	uint8_t ip_part2 = get_number(s2,3);
	
	assert(ip_part == 234);
	assert(ip_part2 == 255);
	
	//test parse_utils.c/take
	const char * full = "abcdefg";
	
	char * part = take(1, 3, full, sizeof(full));
	
	assert(part[0] == full[1]);
	assert(part[2] == full[3]);
	
	free(part);
	
	char * part2 = take(4, 3, full, sizeof(full));
	
	assert(part2[0] == full[4]);
	assert(part2[2] == full[6]);
	
	free(part2);
	
	const char * ip_s = "100.12.3.255";
	
	char * part3 = take(9,3,ip_s,12);	
	
	assert(part3[2] == ip_s[11]);
	
	free(part3);
	
	//test parse_utils.c/parse_ip
	const char * ip_addr = "10.1.0.255";
	
	uint8_t * ip = parse_ip(ip_addr, 10);

	assert(ip[0] == 10);
	assert(ip[1] == 1);
	assert(ip[2] == 0);
	assert(ip[3] == 255);
	
	free(ip);
	
}

struct lpm_trie_key *lpm_trie_key_alloc(size_t prefixlen, uint8_t *data)
{
    struct lpm_trie_key *key = malloc(sizeof(struct lpm_trie_key));
    key->prefixlen = prefixlen;
    memcpy(key->data, data, LPM_DATA_SIZE);
    return key;
}

struct lpm_trie_node *pointer_from_int(int index, struct lpm_trie *trie)
{
    return trie->node_mem_blocks + index;
}

void test_lookup(){
	
	//setup Trie
	
	struct lpm_trie *trie = lpm_trie_alloc(MAX_ROUTES_ENTRIES);
	
	uint8_t data_1[4] = {192, 168, 0, 0};
    struct lpm_trie_key *key_1 = lpm_trie_key_alloc(16, data_1);
    uint8_t data_2[4] = {192, 168, 0, 0};
    struct lpm_trie_key *key_2 = lpm_trie_key_alloc(24, data_2);
	
    
    int res1 = trie_update_elem(trie, key_1, 1);
	int res2 = trie_update_elem(trie, key_2, 2);
	
	if(res1 || res2){
		assert(0);
	}
    
    uint8_t data[4] = {192, 168, 0, 12};
    struct lpm_trie_key *key = malloc(sizeof(struct lpm_trie_key));
	key->prefixlen = 32;
    memcpy(key->data, data, 4 * sizeof(uint8_t));
	
	//Test
	
	int res_1 = trie_lookup_elem(trie, key);
    
    printf("Result is : %d\n", res_1);
    
    assert(res_1 == 2);
    
    free(trie);
    free(key_1);
    free(key_2);
}



void test_insert_in_trie(){
	
	
	FILE * routes = fopen("routes", "r");

	  
    insert_all(routes);
  
  
	if(!lpm_trie){
		assert(0);
	}
    
    
    uint8_t data[4] = {192, 168, 0, 12};
     
    struct lpm_trie_key *key = malloc(sizeof(struct lpm_trie_key));
	key->prefixlen = 32;
    memcpy(key->data, data, 4 * sizeof(uint8_t));
    
    
    uint8_t data_2[4] = {192, 168, 1, 12};
     
    struct lpm_trie_key *key_2 = malloc(sizeof(struct lpm_trie_key));
	key_2->prefixlen = 32;
    memcpy(key_2->data, data_2, 4 * sizeof(uint8_t));
    
    
    uint8_t data_3[4] = {192, 168, 1, 9};
     
    struct lpm_trie_key *key_3 = malloc(sizeof(struct lpm_trie_key));
	key_3->prefixlen = 32;
    memcpy(key_3->data, data_3, 4 * sizeof(uint8_t));
    
    uint8_t data_4[4] = {192, 168, 5, 12};
     
    struct lpm_trie_key *key_4 = malloc(sizeof(struct lpm_trie_key));
	key_4->prefixlen = 32;
    memcpy(key_4->data, data_4, 4 * sizeof(uint8_t));


    int res_1 = trie_lookup_elem(lpm_trie, key);
    
    int res_2 = trie_lookup_elem(lpm_trie, key_2);
    
    int res_3 = trie_lookup_elem(lpm_trie, key_3);
    
    int res_4 = trie_lookup_elem(lpm_trie, key_4);
    
    printf("Result is : %d\n", res_1);
    printf("Result is : %d\n", res_2);
    printf("Result is : %d\n", res_3);
    printf("Result is : %d\n", res_4);
    
    assert(res_1 == 1);
    assert(res_2 == 2);
    assert(res_3 == 3);
    assert(res_4 == 4);
    
	fclose(routes);

	free(lpm_trie);
	free(key);
}




