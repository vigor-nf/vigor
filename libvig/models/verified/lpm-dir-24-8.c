#include "klee/klee.h"
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include "libvig/verified/lpm-dir-24-8.h"
#include "lpm-dir-24-8-control.h"

#define PREALLOC_SIZE (256)
#define NUM_ELEMS (3)

struct lpm {
  lpm_entry_condition *cond;
};

int lpm_allocate(struct lpm **lpm_out) {
  klee_trace_ret();
  klee_trace_param_ptr(lpm_out, sizeof(struct lpm*), "lpm_out");
  int allocation_succeeded = klee_int("lpm_alloc_success");
  if (!allocation_succeeded)
    return 0;
  *lpm_out = malloc(sizeof(struct lpm));
  (**lpm_out).cond = NULL;
  return 1;
}

void lpm_free(struct lpm *lpm) {
  klee_assert(0);//Not supported
}

int lpm_update_elem(struct lpm *lpm, uint32_t prefix,
                    uint8_t prefixlen, uint16_t value) {
  klee_trace_ret();
  klee_trace_param_u64((uint64_t)lpm, "lpm");
  klee_trace_param_u32(prefix, "prefix");
  //VV should be u8, but too lazy to add that to klee
  klee_trace_param_u16(prefixlen, "prefixlen");
  klee_trace_param_u16(value, "value");
  return klee_int("lpm_update_elem_result");
}

int lpm_lookup_elem(struct lpm *lpm, uint32_t prefix) {
  klee_trace_ret();
  klee_trace_param_u64((uint64_t)lpm, "lpm");
  klee_trace_param_u32(prefix, "prefix");
  int val = klee_int("lpm_lookup_reesult");
  if (lpm->cond)
    klee_assume(lpm->cond(prefix, val));
  return val;
}

void lpm_set_entry_condition(struct lpm *lpm, lpm_entry_condition *cond) {
  lpm->cond = cond;
}
