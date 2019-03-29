#include "router.h"

struct router_config config;


struct rte_lpm * lpm_dir;

typedef struct{
	
	uint32_t ip;
	uint16_t port;
	uint8_t dirty;
	
}cache;

cache * ip_cache;


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
		 
        abort();
	}
	

	struct router_config config;
	
	//insert all routes into data structure and returns it. Also fill the ports list (NIC ports)
	insert_all(in_file);
	

	
	if(!lpm_dir){
		fclose(in_file);
		abort();
	}

	ip_cache = calloc(CACHE_SIZE, sizeof(cache));
	
	
	if(ip_cache == NULL){
		abort();
	}
	
    //close file
    fclose(in_file);
    
}


int checkCache(uint32_t ip_addr){
	
	int res = 0;
	
	cache line = ip_cache[ip_addr % CACHE_SIZE];
	
	if(likely(ip_addr == line.ip)){	//check destination in cache
		return line.port;
	}
	else{	//check in directory for lpm
		
		if(unlikely(rte_lpm_lookup (lpm_dir, ip_addr, &res))){	//lookup returns 0 on lookup hit
		
				return FLOOD_FRAME;	// in case of lookup miss
		} 
		
		if(line.dirty == 1){
			
			
			line.port = res;
			line.ip = ip_addr;
			line.dirty = 0;
			
			return res;
		}
		else{
			
			line.dirty = 1;
			return res;
		}
		
	}
}



/**
 * Routes packets using a LPM DIR-24-8
 */
int nf_core_process(struct rte_mbuf* mbuf, vigor_time_t now){
	

	//half of the packets are "bad"...


	//first try
/*
	struct ether_hdr* eth_hdr = nf_then_get_ether_header(mbuf_pkt(mbuf));
	struct ipv4_hdr *  ip_hdr = (struct ipv4_hdr *)(eth_hdr + 1);
*/

	//second try	

	uint8_t* ip_options;
	bool ip_ok = true;
	struct ipv4_hdr * ip_hdr = nf_then_get_ipv4_header(mbuf->buf_addr, &ip_options, &ip_ok);

	/*if(unlikely(!ip_ok)){
		 printf("not a good ip\n"); fflush(stdout);
		return FLOOD_FRAME;
	}*/

//as in l3fwd by dpdk -> SEGV


/*	struct ipv4_hdr *ip_hdr;
        struct ether_hdr *eth_hdr;

        if (RTE_ETH_IS_IPV4_HDR(mbuf->packet_type)) {
                eth_hdr = rte_pktmbuf_mtod(mbuf, struct ether_hdr *);
                //ip_hdr = (struct ipv4_hdr *)(eth_hdr + 1);

		  ip_hdr = rte_pktmbuf_mtod_offset(mbuf, struct ipv4_hdr *, sizeof(struct ether_hdr));


	}
	else{

		return FLOOD_FRAME;
	}

*/

//as in policer

  /*const uint16_t in_port = mbuf->port;
  struct ether_hdr* ether_header = nf_then_get_ether_header(mbuf->buf_addr);

  if (unlikely(!RTE_ETH_IS_IPV4_HDR(mbuf->packet_type) &&
      !(mbuf->packet_type == 0 &&
        ether_header->ether_type == rte_cpu_to_be_16(ETHER_TYPE_IPv4)))) {
    printf("not an ipv4...\n"); fflush(stdout);
    return in_port;
  }

  uint8_t* ip_options;
  bool wellformed = true;
	struct ipv4_hdr* ip_hdr = nf_then_get_ipv4_header(mbuf->buf_addr, &ip_options, &wellformed);
  if (unlikely(!wellformed)) {
	printf("router dropping packet...\n"); fflush(stdout);
    return in_port;
}


*/

    uint32_t ip_addr = rte_be_to_cpu_32(((struct ipv4_hdr *)ip_hdr)->dst_addr); //rte_be_to_cpu_32(ip_hdr->dst_addr);
	
    int res = 0;
  
#ifdef CACHE 
   
    return checkCache(ip_addr);
    
#else	

	if(unlikely(rte_lpm_lookup (lpm_dir, ip_addr, &res))){	//lookup returns 0 on lookup hit
		
		return FLOOD_FRAME;	// in case of lookup miss
	} 
	
	//printf("Route is : %d\n",res); fflush(stdout);
	return res;

#endif
}


/**
 * insert all routes from the csv file to the lpm trie
 */
void insert_all(FILE * f){
	
	
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
	
	
	
	 
    size_t length = 0;
    char * line = NULL;
    int csvLength = 0;

 
	while ((csvLength = getline(&line, &length, f)) >= MIN_ENTRY_SIZE) {
		
    
		uint8_t * ip = NULL;
		uint8_t mask = 0;
		uint8_t port = 0;
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
		
   

		
			uint32_t  * ip_address= malloc(sizeof(uint32_t));
			
			if(!ip_address){
				printf("Could not allocate memory !");
				abort();
			}
			
			memcpy(ip_address, ip, sizeof(uint32_t));
			
			int res = rte_lpm_add(lpm_dir, *ip_address, mask, port);
			
			free(ip_address);
					

		
      
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
