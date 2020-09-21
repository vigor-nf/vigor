#include "ether.h"

#include <klee/klee.h>

struct str_field_descr rte_ether_addr_descrs[] = {
  {offsetof(struct rte_ether_addr, addr_bytes), sizeof(uint8_t ), 6, "addr_bytes"},
};
struct nested_field_descr rte_ether_addr_nests[] = {

};
unsigned rte_ether_addr_hash(void* obj)
{
  klee_trace_ret();
  klee_trace_param_tagged_ptr(obj, sizeof(struct rte_ether_addr),
                             "obj", "rte_ether_addr", TD_BOTH);
  for (int i = 0; i < sizeof(rte_ether_addr_descrs)/sizeof(rte_ether_addr_descrs[0]); ++i) {
    klee_trace_param_ptr_field_arr_directed(obj,
                                            rte_ether_addr_descrs[i].offset,
                                            rte_ether_addr_descrs[i].width,
                                            rte_ether_addr_descrs[i].count,
                                            rte_ether_addr_descrs[i].name,
                                            TD_BOTH);
  }
  for (int i = 0; i < sizeof(rte_ether_addr_nests)/sizeof(rte_ether_addr_nests[0]); ++i) {
    klee_trace_param_ptr_nested_field_arr_directed(obj,
                                                  rte_ether_addr_nests[i].base_offset,
                                                  rte_ether_addr_nests[i].offset,
                                                  rte_ether_addr_nests[i].width,
                                                  rte_ether_addr_nests[i].count,
                                                  rte_ether_addr_nests[i].name,
                                                  TD_BOTH);
  }
  return klee_int("rte_ether_addr_hash");
}
