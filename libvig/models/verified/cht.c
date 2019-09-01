#include "klee/klee.h"
#include "libvig/verified/cht.h"

int cht_fill_cht(struct Vector *cht, uint32_t cht_height,
                 uint32_t backend_capacity) {
  klee_trace_ret();
  klee_trace_param_u64((uint64_t)cht, "cht");
  klee_trace_param_u32(cht_height, "cht_height");
  klee_trace_param_u32(backend_capacity, "backend_capacity");
  // see how long we can run without doing any modelling here
  return klee_int("cht_fill_cht_successful");
}

int cht_find_preferred_available_backend(uint64_t hash, struct Vector *cht,
                                         struct DoubleChain *active_backends,
                                         uint32_t cht_height,
                                         uint32_t backend_capacity,
                                         int *chosen_backend) {
  klee_trace_ret();
  klee_trace_param_u64(hash, "hash");
  klee_trace_param_u64((uint64_t)cht, "cht");
  klee_trace_param_u64((uint64_t)active_backends, "active_backends");
  klee_trace_param_u32(cht_height, "cht_height");
  klee_trace_param_u32(backend_capacity, "backend_capacity");
  klee_trace_param_ptr(chosen_backend, sizeof(int), "chosen_backend");
  if (klee_int("prefered_backend_found")) {
    *chosen_backend = klee_int("chosen_backend");
    klee_assume(0 <= *chosen_backend);
    klee_assume(*chosen_backend < backend_capacity);
    return 1;
  } else {
    return 0;
  }
}
