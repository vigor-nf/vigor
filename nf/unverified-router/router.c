#include "router.h"

struct router_config config;

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
	
	#ifdef TRIE
	
	if(!lpm_trie){
		fclose(in_file);
		abort();
	}
	
	#else
	
	if(!lpm_dir){
		fclose(in_file);
		abort();
	}
	
	#endif
	
    //close file
    fclose(in_file);
    
}



/**
 * Routes packets using a LPM Trie
 */
int nf_core_process(struct rte_mbuf* mbuf, vigor_time_t now){
	
	//retrieve the ip
	struct ether_hdr* eth_hdr = nf_then_get_ether_header(mbuf_pkt(mbuf));
	struct ipv4_hdr *  ip_hdr = (struct ipv4_hdr *)(eth_hdr + 1);
	uint32_t ip_addr = rte_be_to_cpu_32(ip_hdr->dst_addr);
	
    int res = FLOOD_FRAME;
    
#ifdef TRIE	

	struct lpm_trie_key *key = malloc(sizeof(struct lpm_trie_key));
    
    if(unlikely(!key)){
		printf("Couldn't allocate memory !");
		abort();
	}
    
	key->prefixlen = 32 ;
    memcpy(key->data, &ip_addr, IPV4_IP_SIZE * sizeof(uint8_t));
    
	int res = trie_lookup_elem(lpm_trie, key);
	
	
	free(key);
	
#else
	
	if(unlikely(rte_lpm_lookup (lpm_dir, ip_addr, &res))){	//lookup returns 0 on lookup hit
		
		res = FLOOD_FRAME;	// in case of lookup miss
	}
	
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
	
	//inspired by dpdk's l3fwd example

	struct rte_lpm_config config_ipv4;

	char s[64];

	/* create the LPM table */
	config_ipv4.max_rules = MAX_ROUTES_ENTRIES;
	config_ipv4.number_tbl8s = 256;
	config_ipv4.flags = 0;
	snprintf(s, sizeof(s), "IPV4_ROUTER_LPM_%d", 0);
	
	lpm_dir = rte_lpm_create(s, SOCKET_ID_ANY, &config_ipv4);

	
	if (lpm_dir == NULL)
		rte_exit(EXIT_FAILURE,"Unable to create the router LPM table\n");
	
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
		
   
   
		#ifdef TRIE
		
			struct lpm_trie_key *key = lpm_trie_key_alloc(mask, ip);
			int res = trie_update_elem(lpm_trie, key, port);
			
		#else
		
			uint32_t  * ip_address= malloc(sizeof(uint32_t));
			
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


//Needed by nf_main.c

void nf_config_init(int argc, char** argv) {
  router_config_init(&config, argc, argv);
}

void nf_config_cmdline_print_usage(void) {
  router_config_cmdline_print_usage();
}

void nf_print_config() {
  router_print_config(&config);
}
