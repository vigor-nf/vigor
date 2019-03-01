#include "lpm_trie/lpm_trie_mem.h"
#include "parse_utils.h"
#include <stdio.h>
#include <math.h>
#include <ctype.h>

#define CSV_LINE_SIZE 17
#define MAX_ROUTES_ENTRIES 256

int * insert_all(FILE * f, struct lpm_trie * t);
struct lpm_trie_key *lpm_trie_key_alloc(size_t prefixlen, uint8_t *data);
char * take(size_t starting, size_t n, const char * s, size_t length);
void nf_core_process(struct lpm_trie * trie);
struct lpm_trie * nf_core_init(void);

int main( int argc, const char* argv[] ){
	
	
	struct lpm_trie * trie = nf_core_init();
	
	nf_core_process(trie);
	
	
	free(trie);
	trie = NULL;
}

/**
 * Initialize the NF
 */
  struct lpm_trie * nf_core_init(void){
	
	//bind NICs
	
	//create data structure
	

    struct lpm_trie *trie = lpm_trie_alloc(MAX_ROUTES_ENTRIES);
    
	//read routes from file	
	
	FILE *in_file  = fopen("routes", "r");
	
	if(!in_file){
		printf("Error! Could not open file\n"); 
        abort();
	}
	
	//insert all routes into data structure and returns list of values (NIC port)
	
	int* res = insert_all(in_file, trie);
	
	if(!res){
		abort();
	}
    
    //close file
    fclose(in_file);
    
	return trie;
}


/**
 * Routes packets using a LPM Trie
 */
void nf_core_process(struct lpm_trie * trie){
	
	
	
}


/**
 * insert all routes from the csv file to the lpm trie
 */
int * insert_all(FILE * f, struct lpm_trie * t){
	
    size_t length = 0;
    char * line = NULL;
    size_t csvLength = 0;
    
    int * res = calloc(MAX_ROUTES_ENTRIES, sizeof(int));
    if(!res){
		printf("Could not allocate memory !\n");
		return NULL;
	}
	
	while ((csvLength = getline(&line, &length, f)) != -1) {
		
		struct lpm_trie_key *key = malloc(sizeof(struct lpm_trie_key));
		
		if(!key){
			printf("Could not allocate memory !\n");
			return NULL;
		}
    
		uint8_t * ip = NULL;
		uint32_t mask = 0;
		int port = 0;
		int j = 0;
		
		for(size_t i = 0; i < length; ++i){
		
			if(line[i] == ','){
				if( j == 0){
					ip = parse_ip(take(0,i,line, csvLength), i);
					
					if(!ip){
						printf("Error while parsing routes !\n"); 
						return NULL;
					}
					
					j++;
				}
				else if(j == 1){
					//mask = ...
				}
				else{
					//port = ...
					//res[] = ... 
				}
			}
			
		}
    
    
		key->prefixlen = mask;
		memcpy(key->data, ip, IPV4_IP_SIZE);
		
		int res = trie_update_elem(t, key, port);
		
      
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
      
      
		if(ip){
			free(ip);
			ip = NULL;
		}
    }

	
	
	
        
       
    if(line){
		free(line);
		line = NULL;
	}
	
	return res;
}
