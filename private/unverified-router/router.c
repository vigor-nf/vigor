#include "router.h"

struct rte_lpm *lpm_dir;

/**
 * Initialize the NF
 */
void nf_init(void) {

  // read routes from file
  FILE *in_file = fopen("routes", "r");

  if (!in_file) {
    abort();
  }

  // insert all routes into data structure and returns it. Also fill the ports
  // list (NIC ports)
  insert_all(in_file);

  if (!lpm_dir) {
    fclose(in_file);
    abort();
  }

  // close file
  fclose(in_file);
}

/**
 * Routes packets using a LPM DIR-24-8
 */
int nf_process(struct rte_mbuf *mbuf, vigor_time_t now) {

  // as in policer
  const uint16_t in_port = mbuf->port;
  struct ether_hdr *ether_header = nf_then_get_ether_header(mbuf->buf_addr);

  uint8_t *ip_options;
  struct ipv4_hdr *ip_hdr =
      nf_then_get_ipv4_header(ether_header, mbuf_pkt(mbuf), &ip_options);
  if (ip_hdr == NULL) {
    printf("not an ipv4...\n");
    fflush(stdout);
    return in_port;
  }

  uint32_t ip_addr = rte_be_to_cpu_32(((struct ipv4_hdr *)ip_hdr)->dst_addr);
  int res = 0;

  if (unlikely(rte_lpm_lookup(lpm_dir, ip_addr, &res))) { // lookup returns 0 on
                                                          // lookup hit
    return FLOOD_FRAME; // in case of lookup miss
  }

  return res;
}

/**
 * insert all routes from the csv file to the lpm trie
 */
void insert_all(FILE *f) {

  // inspired by dpdk's l3fwd example

  struct rte_lpm_config config_ipv4;
  char s[64];

  // create the lpm table's config
  config_ipv4.max_rules = MAX_ROUTES_ENTRIES;
  config_ipv4.number_tbl8s = MAX_TBL_8;
  config_ipv4.flags = 0;
  snprintf(s, sizeof(s), "IPV4_ROUTER_LPM_%d", 0);

  // create the lpm table
  lpm_dir = rte_lpm_create(s, SOCKET_ID_ANY, &config_ipv4);

  if (lpm_dir == NULL) {
    rte_exit(EXIT_FAILURE, "Unable to create the router LPM table\n");
  }

  // Parsing the routes from the file
  size_t length = 0;
  char *line = NULL;
  int csvLength = 0;

  while ((csvLength = getline(&line, &length, f)) >= MIN_ENTRY_SIZE) {

    // variables for each new routes

    uint8_t *ip = NULL;
    uint8_t mask = 0;
    uint8_t port = 0;
    int j = 0;
    size_t count = 0;
    size_t entries_count = 0;

    for (size_t i = 0; i < csvLength; ++i) {

      if (line[i] == ',') {
        if (j == 0) {
          ip = parse_ip(take(0, i, line, csvLength), i);
          if (!ip) {
            printf("Error while parsing routes !\n");
            abort();
          }
          j++;
          count = 0;
        } else if (j == 1) {
          char *mask_part = take(i - count, count, line, csvLength);

          if (!mask_part) {
            printf("Error while parsing routes !\n");
            abort();
          }
          mask = get_number(mask_part, count);

          if (mask > 32) {
            printf("Error while parsing routes !\n");
            abort();
          }
          count = 0;
        }

      } else if (i == csvLength - 1) {

        char *port_part = take(i - count, count, line, csvLength);

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

    uint32_t *ip_address = malloc(sizeof(uint32_t));

    if (!ip_address) {
      printf("Could not allocate memory !");
      abort();
    }

    // compute ip address from the byte array
    *ip_address = ip[3] + (ip[2] << 8) + (ip[1] << 16) + (ip[0] << 24);

    int res = rte_lpm_add(lpm_dir, *ip_address, mask, port);
    free(ip_address);

    if (res) {
      printf("error during update. error is : %d\n", res);
      fflush(stdout);
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

// needed by nf.h
void nf_config_init(int argc, char **argv) {}
void nf_config_usage(void) {}
void nf_config_print(void) {}
