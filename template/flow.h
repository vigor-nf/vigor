#include <stdint.h>

// ===
// This is a structure used in the NF state.
// Upon compilation, a header and an implementation file will be generated, with
// suffixes '.gen.h' and '.gen.c' respectively. They contain:
// - A hash method, with suffix '_hash' (e.g. 'unsigned FlowId_hash(void*)')
// - An equality method, with suffix '_eq' (e.g. 'bool FlowId_eq(void*)')
// - A log method, with prefix 'log_' (e.g. 'void log_FlowId(void*)')
// - Some necessary implementation details
//
// Due to the prototype nature of Vigor, YOU MUST MANUALLY MIRROR CHANGES TO
// THIS FILE INTO dataspec.ml
// ===

struct FlowId {
  uint16_t src_port;
  uint16_t dst_port;
  uint32_t src_ip;
  uint32_t dst_ip;
  uint8_t protocol;
};
