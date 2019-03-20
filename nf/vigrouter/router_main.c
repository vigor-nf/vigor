#include "router_main.h"

#define IPV4_FULL_MASK 32

struct lpm_trie* routing_table;

/**
 *	lpm trie key allocation made easy 
 */
struct lpm_trie_key* lpm_trie_key_alloc(size_t prefixlen, uint8_t *data)
{
    struct lpm_trie_key* key = malloc(sizeof(struct lpm_trie_key));
    key->prefixlen = prefixlen;
    memcpy(key->data, data, LPM_DATA_SIZE);
    return key;
}

void extract_address_block(struct rte_mbuf* mbuf, struct IPV4_address_block *address_block)
{
	//Extract header
	struct ether_hdr* ether_header = nf_get_ether_header(mbuf_pkt(mbuf));
	
	if(!RTE_ETH_IS_IPV4_HDR(mbuf->packet_type)){
		NF_DEBUG("Not IPv4, dropping packet");
		return 0;
	}
	
	uint8_t* ip_options;
	bool wellformed = true;
	
	struct ipv4_hdr* ipv4_header = nf_then_get_ipv4_header(mbuf_pkt(mbuf), &ip_options, &wellformed);
}



void nf_core_init(void){
	
	//Allocate the table
	routing_table = lpm_trie_alloc(MAX_ROUTES_ENTRIES);
	if(routing_table == 0){
		rte_exit(EXIT_FAILURE, "Error: not enough memory to allocate the routing table");
	}
	
	//Open file containing the routes
	FILE *routing_file = fopen("routes", "r");
	
	if(routing_file == 0){
		rte_exit(EXIT_FAILURE, "Error! Could not open file\n");
	}
	
	//Prepare array for the interfaces to bind
	int *ports = calloc(MAX_ROUTES_ENTRIES, sizeof(int));
    if(!ports){
		rte_exit(EXIT_FAILURE, "Could not allocate memory !\n");
	}
	
	//Populate the LPM routing table
	insert_all(routing_file, routing_table, ports);
	
	//Close file when done
	fclose(routing_file);
}

int nf_core_process(struct rte_mbuf* mbuf, vigor_time_t now)
{
	int dst_device = -1;
	
	//Extract header
	struct ether_hdr* ether_header = nf_get_ether_header(mbuf_pkt(mbuf));
	
	if(!RTE_ETH_IS_IPV4_HDR(mbuf->packet_type)){
		NF_DEBUG("Not IPv4, dropping packet");
		return dst_device;
	}
	
	uint8_t* ip_options;
	bool wellformed = true;
	
	struct ipv4_hdr* ipv4_header = nf_then_get_ipv4_header(mbuf_pkt(mbuf), &ip_options, &wellformed);
	
	if(!wellformed){
		NF_DEBUG("Malformed IPv4, dropping packet");
		return dst_device;
	}
	
	assert(ipv4_header != NULL);
	
	uint8_t ipv4[LPM_DATA_SIZE];
	
	//Parse the 32bits IPv4 into 4*8bits
	memcpy(ipv4, ipv4_header->src_addr, IPV4_FULL_MASK);
	
	//Create the lpm trie key containing the searched ip address block
	struct lpm_trie_key* trie_key_packet_dst_addr = lpm_trie_key_alloc(IPV4_FULL_MASK, ipv4);
	
	//Lookup in the routing table
	dst_device = trie_lookup_elem(routing_table, trie_key_packet_dst_addr);
	
	free(address_block)
	free(trie_key_packet_dst_addr);
	
	return dst_device;
}


// FILE PARSING, NO VERIFICATION
/**
 * insert all routes from the csv file to the lpm trie
 */
void insert_all(FILE* f, struct lpm_trie* routing_table){
	
    size_t length = 0;
    char* line = NULL;
    int csvLength = 0;
    size_t entries_count = 0;
    
 
	while ((csvLength = getline(&line, &length, f)) >= MIN_ENTRY_SIZE) {
		
		uint8_t* ip = NULL;
		uint32_t mask = 0;
		int port = 0;
		int j = 0;
		size_t count = 0;
		
		for(size_t i = 0; i < csvLength; ++i){

			if(line[i] == ','){
				if( j == 0){//Reading IP
					
					ip = parse_ip(take(0,i,line, csvLength), i);

					if(ip == 0){
						rte_exit(EXIT_FAILURE, "Error while parsing IP at line %d !\n", entries_count+1); 
					}
					
					j++;
					count = 0;
				}
				else if(j == 1){//Reading mask
					
					char* mask_part = take(i - count, count, line, csvLength);
					
					if(mask_part == 0){
						rte_exit(EXIT_FAILURE, "Error while parsing mask at line %d !\n", entries_count+1);
					}
					mask =  get_number(mask_part, count);
					
					if( mask > 32){
						rte_exit(EXIT_FAILURE, "Error while parsing mask at line %d ! Mask must be between 0 and 32 !\n", entries_count+1); 
					}
					count = 0;
				}
				
			}else if(i == csvLength -1){//Reading port
				
				if(entries_count >= MAX_ROUTES_ENTRIES){
					rte_exit(EXIT_FAILURE, "Error: too much entries in routes file !\n"); 
				}

				char* port_part = take(i - count , count, line, csvLength);
				
				if(!port_part){
					rte_exit(EXIT_FAILURE, "Error while parsing port at line %d !\n", entries_count+1); 				
				}
	
				port = get_number(port_part, count);

				entries_count++;
				
			}
			else{
				count++;
			}
		}

		struct lpm_trie_key* key = lpm_trie_key_alloc(mask, ip);
		
		if(key == 0){
			rte_exit(EXIT_FAILURE, "Not enough memory to allocate the key!\n");
		}
		
		int res = trie_update_elem(routing_table, key, port);
		free(key);
		
		if(res != 0){
			rte_exit(EXIT_FAILURE, "Error during update : %d\n", res);
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
