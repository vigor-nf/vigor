#include "router.h"

#ifdef TRIE
struct lpm_trie * lpm_trie;
#else

struct rte_lpm * lpm_dir;

#endif

struct lpm_trie_key * lpm_trie_key_alloc(size_t prefixlen, uint8_t *data)
{
    struct lpm_trie_key *key = malloc(sizeof(struct lpm_trie_key));
    key->prefixlen = prefixlen;
    memcpy(key->data, data, LPM_DATA_SIZE);
    return key;
}



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
	
	if(!lpm_trie){
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
	
	 
	struct ether_hdr * eth_hdr = rte_pktmbuf_mtod(mbuf, struct ether_hdr *);
	struct ipv4_hdr *  ip_hdr = (struct ipv4_hdr *)(eth_hdr + 1);
	uint32_t ip_addr = rte_be_to_cpu_32(ip_hdr->dst_addr);
	
    
#ifdef TRIE	

	struct lpm_trie_key *key = malloc(sizeof(struct lpm_trie_key));
    
    if(!key){
		printf("Couldn't allocate memory !");
		abort();
	}
    
	key->prefixlen = 32 ;//get prefix length
    memcpy(key->data, &ip_addr, IPV4_IP_SIZE * sizeof(uint8_t));
    
	uint16_t res = trie_lookup_elem(lpm_trie, key);
	free(key);
	
#else

	uint32_t res = 0;
	rte_lpm_lookup (lpm_dir, ip_addr, &res); 
	
#endif

	return res;
}


/**
 * insert all routes from the csv file to the lpm trie
 */
void insert_all(FILE * f){
	
	#ifdef TRIE
	
	lpm_trie = lpm_trie_alloc(MAX_ROUTES_ENTRIES);
	
	if(!lpm_trie){
		printf("Could not initialize trie !\n");
		abort();
	}
	
	#else
	
	const char * name = "main_lpm_table";
	
	const struct rte_lpm_config * config = malloc(sizeof(struct rte_lpm_config));
	
	if(!config){
		printf("Could not initialize dir-24-8 config file !\n");
		abort();
	}
	
	config->max_rules = MAX_ROUTES_ENTRIES;
	config->number_tbl8s = MAX_TBL_8;
	config->flags = 0;	//unused parameter according to dpdk's doc
	
	lpm_dir =  rte_lpm_create (name, 0, config);
	
	if(!lpm_dir){
		printf("Could not initialize dir-24-8 !\n");
		abort();
	}
	
	
	#endif
	
	
	
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
   
   
		#ifdef TRIE
		
			struct lpm_trie_key *key = lpm_trie_key_alloc(mask, ip);
			int res = trie_update_elem(lpm_trie, key, port);
			
		#else
		
			uint32_t ip_address * = malloc(sizeof(uint32_t));
			
			if(!ip_address){
				printf("Could not allocate memory !");
				abort();
			}
			
			memcpy(ip_address, ip, sizeof(uint32_t));
			
			int res = rte_lpm_add(lpm_dir, *ip_address, mask, port);
			
			free(ip_address);
			
		#endif
		
      
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
