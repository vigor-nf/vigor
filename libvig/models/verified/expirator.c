#include <klee/klee.h>
#include "libvig/verified/expirator.h"
#include "double-chain-control.h"

int expire_items(struct DoubleChain *chain, struct DoubleMap *map,
                 vigor_time_t time) {
  klee_trace_ret();
  klee_trace_param_u64((uint64_t)chain, "chain");
  klee_trace_param_u64((uint64_t)map, "map");
  klee_trace_param_i64(time, "exp_time");
  int nfreed = klee_int("number_of_freed_flows");
  klee_assume(0 <= nfreed);
  dchain_make_space(chain, nfreed);
  // Tell dchain model that we freed some indexes here
  return nfreed;
}

int expire_items_single_map(struct DoubleChain *chain, struct Vector *vector,
                            struct Map *map, vigor_time_t time) {
  klee_trace_ret();
  klee_trace_param_u64((uint64_t)chain, "chain");
  klee_trace_param_u64((uint64_t)vector, "vector");
  klee_trace_param_u64((uint64_t)map, "map");
  klee_trace_param_i64(time, "time");
  int nfreed = klee_int("unmber_of_freed_flows");
  klee_assume(0 <= nfreed);
  dchain_make_space(chain, nfreed);
  return nfreed;
}
