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
     AND id1->protocol  == id2->protocol;
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

  hash = wrap(hash);

  return (unsigned) hash;
}


void flow_extract_keys(void* flow, void** int_id, void** ext_id)
//@ requires [?f]flowp(flow, ?flw) &*& *int_id |-> _ &*& *ext_id |-> _;
/*@ ensures [f]flowp_bare(flow, flw) &*& *int_id |-> ?iidp &*& *ext_id |-> ?eidp &*&
            [f]flow_idp(iidp, ?iid) &*& [f]flow_idp(eidp, ?eid) &*&
            true == flow_ids_offsets_fp(flow, iidp, eidp) &*&
            iid == flow_get_internal_id(flw) &*& eid == flow_get_external_id(flw); @*/
{
  //@ open [f]flowp(flow, flw);
  struct Flow* fl = flow;
  *int_id = &(fl->internal_id);
  *ext_id = &(fl->external_id);
  //@ close [f]flowp_bare(flow, flw);
}

void flow_pack_keys(void* flow, void* iidp, void* eidp)
/*@ requires [?f]flowp_bare(flow, ?flw) &*&
             [f]flow_idp(iidp, ?iid) &*& [f]flow_idp(eidp, ?eid) &*&
             true == flow_ids_offsets_fp(flow, iidp, eidp) &*&
             iid == flow_get_internal_id(flw) &*& eid == flow_get_external_id(flw); @*/
//@ ensures [f]flowp(flow, flw);
{
  IGNORE(flow);
  IGNORE(iidp);
  IGNORE(eidp);
  //@ open flowp_bare(flow, flw);
}

void flow_copy(char* dst, void* src)
//@ requires [?f]flowp(src, ?flw) &*& dst[0..sizeof(struct Flow)] |-> _;
//@ ensures [f]flowp(src, flw) &*& flowp((void*) dst, flw);
{
  struct Flow* source = src;
  struct Flow* destination = (void*) dst;
  //@ close_struct(destination);
  destination->internal_id.src_port = source->internal_id.src_port;
  destination->internal_id.dst_port = source->internal_id.dst_port;
  destination->internal_id.src_ip = source->internal_id.src_ip;
  destination->internal_id.dst_ip = source->internal_id.dst_ip;
  destination->internal_id.protocol = source->internal_id.protocol;
  destination->external_id.src_port = source->external_id.src_port;
  destination->external_id.dst_port = source->external_id.dst_port;
  destination->external_id.src_ip = source->external_id.src_ip;
  destination->external_id.dst_ip = source->external_id.dst_ip;
  destination->external_id.protocol = source->external_id.protocol;
  destination->internal_device = source->internal_device;
}

void flow_destroy(void* flow)
//@ requires flowp(flow, _);
//@ ensures chars(flow, sizeof(struct Flow), _);
{
  IGNORE(flow);
  //@ open flowp(flow, _);
  //@ open_struct((struct Flow*) flow);
}

#ifdef KLEE_VERIFICATION
struct str_field_descr flow_id_descrs[] = {
  {offsetof(struct FlowId, src_port), sizeof(uint16_t), "src_port"},
  {offsetof(struct FlowId, dst_port), sizeof(uint16_t), "dst_port"},
  {offsetof(struct FlowId, src_ip), sizeof(uint32_t), "src_ip"},
  {offsetof(struct FlowId, dst_ip), sizeof(uint32_t), "dst_ip"},
  {offsetof(struct FlowId, protocol), sizeof(uint8_t), "protocol"},
};
struct nested_field_descr flow_nests[] = {
  {offsetof(struct Flow, internal_id), offsetof(struct FlowId, src_port), sizeof(uint16_t), "src_port"},
  {offsetof(struct Flow, internal_id), offsetof(struct FlowId, dst_port), sizeof(uint16_t), "dst_port"},
  {offsetof(struct Flow, internal_id), offsetof(struct FlowId, src_ip), sizeof(uint32_t), "src_ip"},
  {offsetof(struct Flow, internal_id), offsetof(struct FlowId, dst_ip), sizeof(uint32_t), "dst_ip"},
  {offsetof(struct Flow, internal_id), offsetof(struct FlowId, protocol), sizeof(uint8_t), "protocol"},
  {offsetof(struct Flow, external_id), offsetof(struct FlowId, src_port), sizeof(uint16_t), "src_port"},
  {offsetof(struct Flow, external_id), offsetof(struct FlowId, dst_port), sizeof(uint16_t), "dst_port"},
  {offsetof(struct Flow, external_id), offsetof(struct FlowId, src_ip), sizeof(uint32_t), "src_ip"},
  {offsetof(struct Flow, external_id), offsetof(struct FlowId, dst_ip), sizeof(uint32_t), "dst_ip"},
  {offsetof(struct Flow, external_id), offsetof(struct FlowId, protocol), sizeof(uint8_t), "protocol"},
};

struct str_field_descr flow_descrs[] = {
  {offsetof(struct Flow, internal_id), sizeof(struct FlowId), "internal_id"},
  {offsetof(struct Flow, external_id), sizeof(struct FlowId), "external_id"},
  {offsetof(struct Flow, internal_device), sizeof(uint16_t), "internal_device"},
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
  NF_DEBUG(" protocol: %d}",
           id->protocol);
}

void flow_log(struct Flow* flow) {
  NF_DEBUG("{internal_id:");
  flow_log_id(&(flow->internal_id));
  NF_DEBUG(" external_id:");
  flow_log_id(&(flow->external_id));
  NF_DEBUG(" internal_device: %d}", flow->internal_device);
}
#else
void flow_log_ip(uint32_t addr) {
	IGNORE(addr);
}

void flow_log_id(struct FlowId* id) {
	IGNORE(id);
}

void flow_log(struct Flow* flow) {
	IGNORE(flow);
}
#endif
