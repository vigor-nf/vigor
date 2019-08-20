#ifndef _ETHER_ADDR_H_INCLUDED_
#define _ETHER_ADDR_H_INCLUDED_

/* Our current codegenerator does not like all that trash in the rte_ether,
   so we took the struct ether_addr away, as it is needed for some of the NF
   data tuples. */
#ifdef CODEGEN
#  include <stdint.h>
struct ether_addr {
  uint8_t addr_bytes[6];
};
#else // CODEGEN
#  include <rte_ether.h>
#endif // CODEGEN

#endif //_ETHER_ADDR_H_INCLUDED_
