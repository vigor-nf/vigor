#include "nat_flow.h"

#include "lib/ignore.h"

#include <limits.h>
#include <stdlib.h>

// KLEE doesn't tolerate && in a klee_assume (see klee/klee#809),
// so we replace them with & during symbex but interpret them as && in the validator
#ifdef KLEE_VERIFICATION
#  define AND &
#else // KLEE_VERIFICATION
#  define AND &&
#endif // KLEE_VERIFICATION

bool flow_id_eq(void* a, void* b)
//@ requires [?f1]flow_idp(a, ?aid) &*& [?f2]flow_idp(b, ?bid);
//@ ensures [f1]flow_idp(a, aid) &*& [f2]flow_idp(b, bid) &*& (result ? aid == bid : aid != bid);
{
  struct FlowId* id1 = a;
  struct FlowId* id2 = b;
  return id1->src_port  == id2->src_port
     AND id1->dst_port  == id2->dst_port
     AND id1->src_ip    == id2->src_ip
     AND id1->dst_ip    == id2->dst_ip
     AND id1->protocol  == id2->protocol
     AND id1->internal_device == id2->internal_device;
}

static unsigned long long wrap(unsigned long long x)
//@ requires true;
//@ ensures result == _wrap(x) &*& INT_MIN <= result &*& result <= INT_MAX;
{
  //@ div_rem(x, INT_MAX);
  return x % INT_MAX;
}

unsigned flow_id_hash(void* obj)
//@ requires [?f]flow_idp(obj, ?fid);
//@ ensures [f]flow_idp(obj, fid) &*& result == _flow_id_hash(fid);
{
  struct FlowId* id = obj;

  unsigned long long hash = id->src_port;
  hash *= 31;

  hash += id->dst_port;
  hash *= 31;

  hash += id->src_ip;
  hash *= 31;

  hash += id->dst_ip;
  hash *= 31;

  hash += id->protocol;
  hash *= 31;

  hash += id->internal_device;

  hash = wrap(hash);

  return (unsigned) hash;
}

void flow_id_allocate(void* flow_id)
//@ requires chars(flow_id, sizeof(struct FlowId), _);
//@ ensures flow_idp(flow_id, _);
{
  IGNORE(flow_id);
  //@ close_struct((struct FlowId*) flow_id);
  //@ close flow_idp(flow_id, _);
}

#ifdef KLEE_VERIFICATION
struct str_field_descr flow_id_descrs[] = {
  {offsetof(struct FlowId, src_port), sizeof(uint16_t), 0, "src_port"},
  {offsetof(struct FlowId, dst_port), sizeof(uint16_t), 0, "dst_port"},
  {offsetof(struct FlowId, src_ip), sizeof(uint32_t), 0, "src_ip"},
  {offsetof(struct FlowId, dst_ip), sizeof(uint32_t), 0, "dst_ip"},
  {offsetof(struct FlowId, internal_device), sizeof(uint16_t), 0, "internal_device"},
  {offsetof(struct FlowId, protocol), sizeof(uint8_t), 0, "protocol"},
};
#endif//KLEE_VERIFICATION

#ifdef ENABLE_LOG
#include "lib/nf_log.h"
#include <rte_byteorder.h>

void flow_log_ip(uint32_t addr) {
  NF_DEBUG( "%d.%d.%d.%d",
            addr&0xff, (addr>>8)&0xff,
            (addr>>16)&0xff, (addr>>24)&0xff);
}

void flow_log_id(struct FlowId* id) {
  NF_DEBUG( "{src_port: %d(%d); dst_port: %d(%d);\n"
            " src_ip: ",
            id->src_port, rte_be_to_cpu_16(key->src_port),
            id->dst_port, rte_be_to_cpu_16(key->dst_port));
  log_ip(id->src_ip);
  NF_DEBUG( "; dst_ip: ");
  log_ip(id->dst_ip);
  NF_DEBUG(" protocol: %d;",
           id->protocol);
  NF_DEBUG(" internal_device: %d}",
           id->internal_device);
}
#else
void flow_log_id(struct FlowId* id) {
	IGNORE(id);
}
#endif
