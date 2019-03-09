#include <assert.h>
#include "router_main.h"


void test_math();
void test_parse_utils();
void test_insert_in_trie();

int main(){	
	
	//test parse_utils.c
	
	test_parse_utils();
	printf("test_parse_utils ended up well!\n");
	
	//test trie initialization
	test_insert_in_trie();
	printf("test_insert_in_trie ended up well!\n");
	
	
	test_lookup();
	printf("test_lookup ended up well!\n");
	
	return 0;
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


void test_insert_in_trie(){
	
	
	FILE * routes = fopen("routes", "r");
	
	
    struct lpm_trie *trie = lpm_trie_alloc(MAX_ROUTES_ENTRIES);
    
    insert_all(routes, trie);
 
    
	fclose(routes);
	
	uint8_t data1[4] = {192, 168, 5, 12};
	struct lpm_trie_key *key1 = lpm_trie_key_alloc(32, data1);
	
	int res1 = trie_lookup_elem(trie, key1);
	printf("%d\n", res1);

	free(trie);
}

void test_lookup(){
	
	//setup Trie
	
	struct lpm_trie *trie = lpm_trie_alloc(MAX_ROUTES_ENTRIES);
	
	uint8_t data_1[4] = {192, 168, 0, 0};
    struct lpm_trie_key *key_1 = lpm_trie_key_alloc(16, data_1);
    uint8_t data_2[4] = {192, 168, 0, 0};
    struct lpm_trie_key *key_2 = lpm_trie_key_alloc(24, data_2);
    uint8_t data_3[4] = {192, 168, 5, 12};
    struct lpm_trie_key *key_3 = lpm_trie_key_alloc(32, data_3);
    
    int res1 = trie_update_elem(trie, key_1, 1);
    int res2 = trie_update_elem(trie, key_2, 2);
	int res3 = trie_update_elem(trie, key_3, 3);
	
	if(res1 || res2 || res3){
		assert(0);
	}
    
    uint8_t data[4] = {192, 168, 5, 12};
    struct lpm_trie_key *key = lpm_trie_key_alloc(32, data);

	
	//Test
	
	int res_1 = trie_lookup_elem(trie, key);
    
    printf("Result is : %d\n", res_1);
    
    assert(res_1 == 3);
    
    free(trie);
    free(key_1);
    free(key_2);
    free(key_3);
}




