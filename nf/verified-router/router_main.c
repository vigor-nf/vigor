#include "router_main.h"

struct lpm_trie_key *lpm_trie_key_alloc(size_t prefixlen, uint8_t *data);
int *insert_all(FILE * f, struct lpm_trie * t);

void nf_core_init(void){
	
	//Allocate the table
	struct lpm_trie *routing_table = lpm_trie_alloc(MAX_ENTRY_SIZE);
	if(routing_table == 0){
		printf("Error: not enough memory to allocate the routing table");
		abort();
	}
	
	//Open file containing the routes
	FILE *routing_file = fopen("routes", "r");
	
	if(routing_file == 0){
		printf("Error! Could not open file\n");
		abort();
	}
	
	//Populate the LPM routing table
	int *interfaces_to_bind = insert_all(routing_file, routing_table);
	
	//Close file when done
	fclose(routing_file);
}

//int nf_core_process(struct rte_mbuf){}

struct lpm_trie_key *lpm_trie_key_alloc(size_t prefixlen, uint8_t *data)
{
    struct lpm_trie_key *key = malloc(sizeof(struct lpm_trie_key));
    key->prefixlen = prefixlen;
    memcpy(key->data, data, LPM_DATA_SIZE);
    return key;
}

/**
 * insert all routes from the csv file to the lpm trie
 */
int *insert_all(FILE * f, struct lpm_trie *routing_table){
	
    size_t length = 0;
    char * line = NULL;
    int csvLength = 0;
    size_t entries_count = 0;
    
    int *ports = calloc(MAX_ENTRY_SIZE, sizeof(int));
    if(!ports){
		printf("Could not allocate memory !\n");
		abort();
	}
 
	while ((csvLength = getline(&line, &length, f)) >= MIN_ENTRY_SIZE) {
		
		uint8_t *ip = NULL;
		uint32_t mask = 0;
		int port = 0;
		int j = 0;
		size_t count = 0;
		
		for(size_t i = 0; i < csvLength; ++i){

			if(line[i] == ','){
				if( j == 0){//Reading IP
					
					ip = parse_ip(take(0,i,line, csvLength), i);

					if(ip == 0){
						printf("Error while parsing IP at line %d !\n", entries_count+1); 
						abort();
					}
					
					j++;
					count = 0;
				}
				else if(j == 1){//Reading mask
					
					char *mask_part = take(i - count, count, line, csvLength);
					
					if(mask_part == 0){
						printf("Error while parsing mask at line %d !\n", entries_count+1); 
						abort();
					}
					mask =  get_number(mask_part, count);
					
					if( mask > 32){
						printf("Error while parsing mask at line %d ! Mask must be between 0 and 32 !\n", entries_count+1); 
						abort();
					}
					count = 0;
				}
				
			}else if(i == csvLength -1){//Reading port
				
				if(entries_count >= MAX_ENTRY_SIZE){
					printf("Error: too much entries in routes file !\n"); 
					return NULL;
				}

				char *port_part = take(i - count , count, line, csvLength);
				
				if(!port_part){
					printf("Error while parsing port at line %d !\n", entries_count+1); 
					return NULL;				
				}
	
				port = get_number(port_part, count);

				ports[entries_count] = port;
				entries_count++;
				
			}
			else{
				count++;
			}
		}

		struct lpm_trie_key *key = lpm_trie_key_alloc(mask, ip);
		
		if(key == 0){
			printf("Not enough memory to allocate the key!\n");
			abort();
		}
		
		int res = trie_update_elem(routing_table, key, port);
		printf("AAAAAAAAAAAAAH %d\n", res);fflush(stdout);
		free(key);
      
		if(ip){
			free(ip);
			ip = NULL;
		}
    }
   
    if(line){
		free(line);
		line = NULL;
	}
	
	return ports;
}
