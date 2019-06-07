#include "router.h"

struct lpm * lpm_table;

/**
 * Initialize the NF
 */
void nf_core_init(void) {

  //read routes from file		
  FILE *in_file  = fopen("routes", "r");
	
  if (!in_file) {		 
    abort();
  }
	
  //insert all routes into data structure and returns it. Also fill the ports list (NIC ports)
  insert_all(in_file);
		
  if (lpm_table == NULL) {
    fclose(in_file);
    abort();
  }
	
  //close file
  fclose(in_file);    
}

/**
 * Routes packets using a LPM DIR-24-8
 */
int nf_core_process(struct rte_mbuf* mbuf, vigor_time_t now) {
		
//as in policer

  const uint16_t in_port = mbuf->port;
  struct ether_hdr* ether_header = nf_then_get_ether_header(mbuf->buf_addr);

  if (unlikely(!RTE_ETH_IS_IPV4_HDR(mbuf->packet_type) &&
      !(mbuf->packet_type == 0 &&
      ether_header->ether_type == rte_cpu_to_be_16(ETHER_TYPE_IPv4)))) {			
    printf("not an ipv4...\n");
    fflush(stdout);
    return in_port;
  }

  uint8_t* ip_options;
  bool wellformed = true;
  struct ipv4_hdr* ip_hdr = nf_then_get_ipv4_header(mbuf->buf_addr, &ip_options, &wellformed);
	
  if (unlikely(!wellformed)) {
    printf("router dropping packet...\n");
    fflush(stdout);
    return in_port;
  }

  uint32_t ip_addr = rte_be_to_cpu_32(((struct ipv4_hdr *)ip_hdr)->dst_addr); 	
	
  //lookup the ip
  int res = lpm_lookup_elem(lpm_table, ip_addr);

  if (unlikely(res == -1)) {//lookup returns 0 on lookup hit	
    return FLOOD_FRAME;// in case of lookup miss
  }
	
  return res;
}


/**
 * insert all routes from the csv file to the lpm trie
 */
void insert_all(FILE * f) {
	
  //create lpm table
  lpm_table = lpm_allocate();
	
  if (lpm_table == NULL) {
    rte_exit(EXIT_FAILURE,"Unable to create the router LPM table\n");
  }
		
  //Begin parsing the routes 
  size_t length = 0;
  char * line = NULL;
  int csvLength = 0;

  while ((csvLength = getline(&line, &length, f)) >= MIN_ENTRY_SIZE) {		
    //variables for each route
    uint8_t * ip = NULL;
    uint8_t mask = 0;
    uint8_t port = 0;
    int j = 0;
    size_t count = 0;
    size_t entries_count = 0;
		
    for (size_t i = 0; i < csvLength; ++i) {
      if (line[i] == ',') {
        if ( j == 0) {
          ip = parse_ip(take(0,i,line, csvLength), i);

          if (!ip) {
            printf("Error while parsing routes !\n"); 
            abort();
          }
					
          j++;
          count = 0;
        } else if (j == 1) {
          char * mask_part = take(i - count, count, line, csvLength);
					
          if (!mask_part) {
            printf("Error while parsing routes !\n"); 
            abort();
          }

          mask =  get_number(mask_part, count);
					
          if (mask > 32) {
            printf("Error while parsing routes !\n"); 
            abort();
          }

          count = 0;
        }			
      } else if (i == csvLength - 1) {
        char * port_part = take(i - count , count, line, csvLength);
				
        if (!port_part) {
          printf("Error while parsing routes !\n"); 
          abort();				
        }
	
        port = get_number(port_part, count);
				
      } else {
        count++;
      }
    }
		
    entries_count++;
		
    if (entries_count >= MAX_ROUTES_ENTRIES) {
      printf("Error too much entries in routes file !\n"); 
      abort();
    }			
		
    uint32_t ip_address = ip[3] + (ip[2] << 8) + (ip[1] << 16) + (ip[0] <<24);		
		
    //create new key for the lpm table
    struct rule * new_rule = malloc(sizeof(struct rule));
			
    if (new_rule == NULL) {
      printf("Error during update. Could not allocate memory for key !\n");
      abort();
    }
			
    new_rule->ipv4 = ip_address;
    new_rule->prefixlen = mask;
    new_rule->route = (uint16_t)port;

    //update the table with the new key
    int res = lpm_update_elem(lpm_table, new_rule);
   
    if (res == -1) {
      printf("error during update. error is : %d\n",res); fflush(stdout);
      abort();
    }

    if (ip) {
      free(ip);
      ip = NULL;
    }
  }
  
  if (line) {
    free(line);
    line = NULL;
  }
}

//Needed by nf_main.c

void nf_config_init(int argc, char** argv) {

}

void nf_config_cmdline_print_usage(void) {

}

void nf_print_config() {

}
