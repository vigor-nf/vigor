#include "nat_flow.h"

#include "lib/ignore.h"

#include <limits.h>

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
//@ requires [?f]flow_idp(obj, ?id);
//@ ensures [f]flow_idp(obj, id) &*& result == _flow_id_hash(k);
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
/*@ requires [?f]flowp(flow, ?flw) &*& *int_id |-> _ &*& *ext_id |-> _;
    ensures [f]flowp(flwp, flw) &*& *int_id |-> ?iidp &*& *ext_id |-> ?eidp &*&
            [f]flow_idp(&(flow->id), ?iid) &*& [f]flow_idp(iidp, iid) &*& [f]flow_idp(eidp, ?eid) &*&
            eid == flid(flow->id.dst_port, flow->nat_port, flow->id.dst_ip, flow->nat_ip, flow->id.protocol); @*/
{
  //@ open [f]flowp(flow, flw);
  struct Flow* f = flow;
  *int_id = &(f->id);
  *ext_id = malloc(sizeof(struct FlowId));
  (*ext_id)->src_port = f->id.dst_port;
  (*ext_id)->dst_port = f->nat_port;
  (*ext_id)->src_ip = f->id.dst_ip;
  (*ext_id)->dst_ip = f->nat_ip;
  (*ext_id)->protocol = f->id.protocol;
  //@ close [f]flowp(flow, flw);
}

void flow_pack_keys(void* flow, void* iidp, void* eidp)
/*@ requires [?f]flowp(flow, ?flw) &*&
             [f]flow_idp(iidp, ?iid) &*& [f]flow_idp(eidp, ?eid) &*&
             [f]flow_idp(&(flow->id), ?iid) &*& [f]flow_idp(iidp, iid) &*& [f]flow_idp(eidp, ?eid) &*&
            eid == flid(flow->id.dst_port, flow->nat_port, flow->id.dst_ip, flow->nat_ip, flow->id.protocol);
    ensures [f]flowp(flow, flw); @*/
{
  IGNORE(flow);
  IGNORE(iidp);
  free(eidp);
  //@ open flowp(flow, flw);
}

void flow_cpy(char* dst, void* src)
//@ requires [?f]flowp(src, ?flw) &*& dst[0..sizeof(struct Flow)] |-> _;
//@ ensures [f]flowp(src, flw) &*& flowp((void*) dst, flw);
{
  struct Flow* source = src;
  struct Flow* destination = (void*) dst;
  //@ close_struct(destination);
  destination->id.src_port = source->id.src_port;
  destination->id.dst_port = source->id.dst_port;
  destination->id.src_ip = source->id.src_ip;
  destination->id.dst_ip = source->id.dst_ip;
  destination->ik.protocol = source->id.protocol;
  destination->nat_port = source->nat_port;
  destination->nat_ip = source->nat_ip;
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
  {offsetof(struct Flow, id), offsetof(struct FlowId, src_port), sizeof(uint16_t), "src_port"},
  {offsetof(struct Flow, id), offsetof(struct FlowId, dst_port), sizeof(uint16_t), "dst_port"},
  {offsetof(struct Flow, id), offsetof(struct FlowId, src_ip), sizeof(uint32_t), "src_ip"},
  {offsetof(struct Flow, id), offsetof(struct FlowId, dst_ip), sizeof(uint32_t), "dst_ip"},
  {offsetof(struct Flow, id), offsetof(struct FlowId, protocol), sizeof(uint8_t), "protocol"},
};

struct str_field_descr flow_descrs[] = {
  {offsetof(struct Flow, id), sizeof(struct FlowId), "id"},
  {offsetof(struct Flow, nat_port), sizeof(uint16_t), "nat_port"},
  {offsetof(struct flow, nat_ip), sizeof(uint32_t), "nat_ip"},
  {offsetof(struct flow, internal_device), sizeof(uint16_t), "internal_device"},
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
  NF_DEBUG("{id:");
  flow_log_id(&(flow->id));
  NF_DEBUG(" nat_port: %d(%d), nat_ip: ", flow->nat_port, rte_be_to_cpu_16(flow->nat_port));
  flow_log_ip(flow->nat_ip);
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
