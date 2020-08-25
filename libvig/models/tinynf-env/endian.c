#include "env/endian.h"

#if __BYTE_ORDER == __BIG_ENDIAN
uint16_t tn_cpu_to_le16(uint16_t val) { return ((val << 8) & 0xFF) | ((val >> 8) & 0xFF); }
uint16_t tn_le_to_cpu16(uint16_t val) { return ((val << 8) & 0xFF) | ((val >> 8) & 0xFF); }
uint32_t tn_cpu_to_le32(uint32_t val) { return ((val << 24) & 0xFF) | ((val << 8) & 0xFF) | ((val >> 8) & 0xFF) | ((val >> 24) & 0xFF); }
uint32_t tn_le_to_cpu32(uint32_t val) { return ((val << 24) & 0xFF) | ((val << 8) & 0xFF) | ((val >> 8) & 0xFF) | ((val >> 24) & 0xFF); }
uint64_t tn_cpu_to_le64(uint64_t val) { return ((val << 56) & 0xFF) | ((val << 40) & 0xFF) | ((val << 24) & 0xFF) | ((val << 8) & 0xFF) | ((val >> 8) & 0xFF) | ((val >> 24) & 0xFF) | ((val >> 40) & 0xFF) | ((val >> 56) & 0xFF); }
uint64_t tn_le_to_cpu64(uint64_t val) { return ((val << 56) & 0xFF) | ((val << 40) & 0xFF) | ((val << 24) & 0xFF) | ((val << 8) & 0xFF) | ((val >> 8) & 0xFF) | ((val >> 24) & 0xFF) | ((val >> 40) & 0xFF) | ((val >> 56) & 0xFF); }
#else
uint16_t tn_cpu_to_le16(uint16_t val) { return val; }
uint16_t tn_le_to_cpu16(uint16_t val) { return val; }
uint32_t tn_cpu_to_le32(uint32_t val) { return val; }
uint32_t tn_le_to_cpu32(uint32_t val) { return val; }
uint64_t tn_cpu_to_le64(uint64_t val) { return val; }
uint64_t tn_le_to_cpu64(uint64_t val) { return val; }
#endif
