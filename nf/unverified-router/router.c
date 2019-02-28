#include "lpm_trie/lpm_trie_mem.h"
#include <stdio.h>
#include <math.h>
#include <ctype.h>

#define IPV4_IP_SIZE 4
#define CSV_LINE_SIZE 17

int insert_all(FILE * f, struct lpm_trie * t);
struct lpm_trie_key *lpm_trie_key_alloc(size_t prefixlen, uint8_t *data);
char * take(size_t starting, size_t n, const char * s, size_t length);

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
	
	int res = insert_all(in_file, trie);
	
	if(res != 0){
		exit(-1);
	}
    
    //close file
    fclose(in_file);
    
	//forward packets
	
	
	free(trie);
	trie = NULL;
}

/**
 * Transform a small string in an integer between 0-255
 */
uint8_t get_number(const char * s, size_t size){
	
	int buffer = 0;
	
	for(size_t i = 0; i < size; ++i){
		
		if(! isdigit(s[i])){
			printf("Error while parsing routes, invalid ip !\n"); 
			exit(-1);
		}
		
		buffer += pow(10,size -i -1);
	}
	if(buffer > 255){
		
		printf("Error while parsing routes, invalid ip !\n"); 
		exit(-1);
	}
	
	return (uint8_t)buffer;
}

/**
 * Transform a string that represents an ip address in a list of integers between 0-255
 */
uint8_t * parse_ip(char * ip, size_t size){

	if(ip == NULL){
		return NULL;
	}
	
	uint8_t * res = calloc(IPV4_IP_SIZE, sizeof(uint8_t));
	
	if(! res){
		return NULL;
	}
	
	size_t count = 0;
	size_t j = 0;
	
	for(size_t i = 0; i < size; ++i){
		
		if(ip[i] == '.'){
				
			res[j] = get_number(take(i - count -1, count, ip, size), count);
			count = 0;
			j++;
		}
		count++;
		
	}
	
	free(ip);
	ip = NULL;
	
	return res;
	
}

/**
 * Takes n elements of a string of size = length starting at index = starting
 */
char * take(size_t starting, size_t n, const char * s, size_t length){
	
	char * res = calloc(n, sizeof(char));
	if(!res || n + starting > length){
		return NULL;
	}
	
	for(size_t i = starting; i < n; ++i){
		
		res[i] = s[i];
	}
	
	return res;
}

/**
 * insert all routes from the csv file to the lpm trie
 */
int insert_all(FILE * f, struct lpm_trie * t){
	
    size_t length = 0;
    char * line = NULL;
    size_t csvLength = 0;
    
	
	while ((csvLength = getline(&line, &length, f)) != -1) {
		
		struct lpm_trie_key *key = malloc(sizeof(struct lpm_trie_key));
		
		if(!key){
			printf("Could not allocate memory !\n");
			return -1;
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
						return -1;
					}
					
					j++;
				}
				else if(j == 1){
					//mask = 
				}
				else{
					//port = 
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
	
	return 0;
}
