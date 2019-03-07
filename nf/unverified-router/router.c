

#include "router.h"


struct lpm_trie_key *lpm_trie_key_alloc(size_t prefixlen, uint8_t *data);
void nf_core_process(struct lpm_trie * trie);
struct lpm_trie * nf_core_init(void);

/*
int main(){		router doesn't necessarily needs to be executable (can be called from an other file e.g: tests.c)
	
	
	struct lpm_trie * trie = nf_core_init();
	
	nf_core_process(trie);
	
	
	free(trie);
	trie = NULL;
	
	return 0;
}*/




/**
 * Initialize the NF
 */
  struct lpm_trie * nf_core_init(void){
	
	
    
	//read routes from file	
	
	FILE *in_file  = fopen("routes", "r");
	
	if(!in_file){
		printf("Error! Could not open file\n"); 
        abort();
	}
	
	
	
	int * ports = calloc(MAX_ROUTES_ENTRIES, sizeof(int));
	
	if(!ports){
		fclose(in_file);
		abort();
	}
	
	//insert all routes into data structure and returns it. Also fill the ports list (NIC ports)
	struct lpm_trie *trie = insert_all(in_file, ports);
	
	if(!trie){
		fclose(in_file);
		abort();
	}
	
	
	//bind NICs
	
	
    
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
struct lpm_trie * insert_all(FILE * f, int * ports){
	
	struct lpm_trie *trie = lpm_trie_alloc(MAX_ROUTES_ENTRIES);
	
	if(!trie){
		printf("Could not initialize trie !\n");
		return NULL;
	}
	
    size_t length = 0;
    char * line = NULL;
    int csvLength = 0;
    size_t entries_count = 0;

 
	while ((csvLength = getline(&line, &length, f)) >= MIN_ENTRY_SIZE) {
		
    
		uint8_t * ip = NULL;
		uint32_t mask = 0;
		int port = 0;
		int j = 0;
		size_t count = 0;
		
		for(size_t i = 0; i < csvLength; ++i){

			if(line[i] == ','){
				if( j == 0){
					
					ip = parse_ip(take(0,i,line, csvLength), i);

					if(!ip){
						printf("Error while parsing routes !\n"); 
						return NULL;
					}
					
					j++;
					count = 0;
				}
				else if(j == 1){
					
					char * mask_part = take(i - count, count, line, csvLength);
					
					if(!mask_part){
						printf("Error while parsing routes !\n"); 
						return NULL;
					}
					mask =  get_number(mask_part, count);
					
					if( mask > 32){
						printf("Error while parsing routes !\n"); 
						return NULL;
					}
					count = 0;
				}
				
			}else if(i == csvLength -1){
				
				if(entries_count >= MAX_ROUTES_ENTRIES){
					printf("Error too much entries in routes file !\n"); 
					return NULL;
				}

				char * port_part = take(i - count , count, line, csvLength);
				
				if(!port_part){
					printf("Error while parsing routes !\n"); 
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
		
		printf("The mask is : %u \n", mask);
		printf("The ip is : %u", ip[0]);
		printf(".%u", ip[1]);
		printf(".%u", ip[2]);
		printf(".%u \n", ip[3]);
		printf("Port is : %d\n", port);
		
		fflush(stdout);
   
		struct lpm_trie_key *key = lpm_trie_key_alloc(mask, ip);
		
		int res = trie_update_elem(trie, key, port);
      
		if(res){
			printf("error during update. error is : %d\n",res); fflush(stdout);
			return NULL;
		}
      
		if(ip){
			free(ip);
			ip = NULL;
		}
    }

	
	
	
        
       
    if(line){
		free(line);
		line = NULL;
	}
	
	return trie;
	

}
