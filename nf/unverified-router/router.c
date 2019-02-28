#include "lpm_trie/lpm_trie_mem.h"
#include <stdio.h>

#define IPV4_IP_SIZE 4
#define CSV_LINE_SIZE 17

int insert_all(FILE * f, struct lpm_trie * t);
struct lpm_trie_key *lpm_trie_key_alloc(size_t prefixlen, uint8_t *data);

int main( int argc, const char* argv[] ){
	
	
	//bind NICs
	
	//create data structure
	
	size_t max_entries = 256;

    struct lpm_trie *trie = lpm_trie_alloc(max_entries);
    
	//read routes from file	
	
	FILE *in_file  = fopen("routes", "r");
	
	if(!in_file){
		printf("Error! Could not open file\n"); 
        exit(-1);
	}
	
	//insert all routes into data structure
	
	int res = insert_all(in_file, trie)
    
    //close file
    fclose(in_file);
    
	//forward packets
	
	
	free(trie);
	trie = NULL;
}




int insert_all(FILE * f, struct lpm_trie * t){
	
    size_t length = 0;
    char * line = NULL;
    size_t csvLength = 0;
    
	
	while ((csvLength = getline(line, &lenght, f)) == CSV_LINE_SIZE) {
		
		struct lpm_trie_key *key = malloc(sizeof(struct lpm_trie_key));
    
		uint8_t * ip = calloc(IPV4_IP_SIZE, sizeof(uint8_t);
		uint32_t mask = 0;
		int port = 0;
		int j = 0;
		
		for(size_t i = 0; i < length; ++i){
		
			if(csv[i] == ','){
				if( j == 0){
					ip = parse_ip()
					j++;
				}
				else if(j == 1){
					mask = 
				}
				else{
					port = 
				}
			}
			
		}
    
    
		key->prefixlen = mask;
		memcpy(key->data, ip, IPV4_IP_SIZE);
		
		int res = trie_update_elem(t, key_1, value_1);
      
      
      
    }

	
	
	
	/*
	int value_1 = 1;
    int res = trie_update_elem(t, key_1, value_1);
    if(res)
        //error

    struct lpm_trie_node *node_1 = pointer_from_int(t->root, t);
    res = memcmp(node_1->data, key_1->data, LPM_DATA_SIZE);
    if(res)
        //error
  
  
        */
        
        
       
    if(line){
		free(line);
		line = NULL;
	}
	
	return 0;
}
