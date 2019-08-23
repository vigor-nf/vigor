#include "ether.h"

#include <klee/klee.h>

struct str_field_descr ether_addr_descrs[] = {
  {offsetof(struct ether_addr, addr_bytes), sizeof(uint8_t ), 6, "addr_bytes"},
};
struct nested_field_descr ether_addr_nests[] = {

};
unsigned ether_addr_hash(void* obj)
{
  klee_trace_ret();
  klee_trace_param_tagged_ptr(obj, sizeof(struct ether_addr),
                             "obj", "ether_addr", TD_BOTH);
  for (int i = 0; i < sizeof(ether_addr_descrs)/sizeof(ether_addr_descrs[0]); ++i) {
    klee_trace_param_ptr_field_arr_directed(obj,
                                            ether_addr_descrs[i].offset,
                                            ether_addr_descrs[i].width,
                                            ether_addr_descrs[i].count,
                                            ether_addr_descrs[i].name,
                                            TD_BOTH);
  }
  for (int i = 0; i < sizeof(ether_addr_nests)/sizeof(ether_addr_nests[0]); ++i) {
    klee_trace_param_ptr_nested_field_arr_directed(obj,
                                                  ether_addr_nests[i].base_offset,
                                                  ether_addr_nests[i].offset,
                                                  ether_addr_nests[i].width,
                                                  ether_addr_nests[i].count,
                                                  ether_addr_nests[i].name,
                                                  TD_BOTH);
  }
  return klee_int("ether_addr_hash");
}
