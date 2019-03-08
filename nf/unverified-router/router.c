

#include "router.h"


struct lpm_trie_key *lpm_trie_key_alloc(size_t prefixlen, uint8_t *data);


struct lpm_trie *trie = NULL;		//the Trie that will be used by the nf (global variable)


/**
 * Initialize the NF
 */
  void nf_core_init(void){
    
	//read routes from file	
	
	FILE *in_file  = fopen("routes", "r");
	
	if(!in_file){
		printf("Error! Could not open file\n"); 
        abort();
	}
	
	
	//insert all routes into data structure and returns it. Also fill the ports list (NIC ports)
	insert_all(in_file);
	
	if(!trie){
		fclose(in_file);
		abort();
	}
	
    //close file
    fclose(in_file);
    
}



/**
 * Routes packets using a LPM Trie
 */
uint16_t nf_core_process(struct rte_mbuf* mbuf, vigor_time_t now){
	
	 
	struct ether_hdr * eth_hdr = rte_pktmbuf_mtod(m, struct ether_hdr *);
	struct ipv4_hdr *  ip_hdr = (struct ipv4_hdr *)(eth_hdr + 1);

	
    struct lpm_trie_key *key = malloc(sizeof(struct lpm_trie_key));
    
    if(!key){
		printf("Couldn't allocate memory !");
		abort();
	}
    
	key->prefixlen = 32 //get prefix length
    memcpy(key->data, ip_hdr->dst_addr, IPV4_IP_SIZE * sizeof(uint8_t));
	
	
	uint16_t res = trie_lookup_elem(trie, key);
	
	free(key);
	
	return res;
}


/**
 * insert all routes from the csv file to the lpm trie
 */
void insert_all(FILE * f){
	
	trie = lpm_trie_alloc(MAX_ROUTES_ENTRIES);
	
	if(!trie){
		printf("Could not initialize trie !\n");
		abort();
	}
	
    size_t length = 0;
    char * line = NULL;
    int csvLength = 0;

 
	while ((csvLength = getline(&line, &length, f)) >= MIN_ENTRY_SIZE) {
		
    
		uint8_t * ip = NULL;
		uint32_t mask = 0;
		int port = 0;
		int j = 0;
		size_t count = 0;
		size_t entries_count = 0;
		
		for(size_t i = 0; i < csvLength; ++i){

			if(line[i] == ','){
				if( j == 0){
					
					ip = parse_ip(take(0,i,line, csvLength), i);

					if(!ip){
						printf("Error while parsing routes !\n"); 
						abort();
					}
					
					j++;
					count = 0;
				}
				else if(j == 1){
					
					char * mask_part = take(i - count, count, line, csvLength);
					
					if(!mask_part){
						printf("Error while parsing routes !\n"); 
						abort();
					}
					mask =  get_number(mask_part, count);
					
					if( mask > 32){
						printf("Error while parsing routes !\n"); 
						abort();
					}
					count = 0;
				}
				
			}else if(i == csvLength -1){

				char * port_part = take(i - count , count, line, csvLength);
				
				if(!port_part){
					printf("Error while parsing routes !\n"); 
					abort();				
				}
	
				port = get_number(port_part, count);
				
			}
			else{
				count++;
			}
		}
		
		entries_count++;
		
		if(entries_count >= MAX_ROUTES_ENTRIES){
					printf("Error too much entries in routes file !\n"); 
					abort();
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
			abort();
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

}
