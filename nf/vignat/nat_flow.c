#include "nat_flow.h"

#include <stdbool.h>
#include <string.h>
#include <limits.h>

// for RTE_MAX_ETHPORTS
#include <rte_config.h>

#include "lib/ignore.h"

#include "include_ignored_by_verifast.h"

// KLEE doesn't tolerate && in a klee_assume (see klee/klee#809),
// so we replace them with & during symbex but interpret them as && in the validator
#ifdef KLEE_VERIFICATION
#  define AND &
#else // KLEE_VERIFICATION
#  define AND &&
#endif // KLEE_VERIFICATION

bool int_key_eq(void* a, void* b)
//@ requires [?f1]int_k_p(a, ?ak) &*& [?f2]int_k_p(b, ?bk);
//@ ensures [f1]int_k_p(a, ak) &*& [f2]int_k_p(b, bk) &*& (false == result ? (ak != bk) : (ak == bk));
{
  struct int_key* k1 = a;
  struct int_key* k2 = b;
  return k1->int_src_port  == k2->int_src_port
     AND k1->dst_port      == k2->dst_port
     AND k1->int_src_ip    == k2->int_src_ip
     AND k1->dst_ip        == k2->dst_ip
     AND k1->int_device_id == k2->int_device_id
     AND k1->protocol      == k2->protocol;
}

bool ext_key_eq(void* a, void* b)
//@ requires [?f1]ext_k_p(a, ?ak) &*& [?f2]ext_k_p(b, ?bk);
//@ ensures [f1]ext_k_p(a, ak) &*& [f2]ext_k_p(b, bk) &*& (false == result ? (ak != bk) : (ak == bk));
{
  struct ext_key* k1 = a;
  struct ext_key* k2 = b;
  return k1->ext_src_port  == k2->ext_src_port
     AND k1->dst_port      == k2->dst_port
     AND k1->ext_src_ip    == k2->ext_src_ip
     AND k1->dst_ip        == k2->dst_ip
     AND k1->ext_device_id == k2->ext_device_id
     AND k1->protocol      == k2->protocol;
}

static unsigned long long wrap(unsigned long long x)
//@ requires true;
//@ ensures result == _wrap(x) &*& INT_MIN <= result &*& result <= INT_MAX;
{
  //@ div_rem(x, INT_MAX);
  return x % INT_MAX;
}

unsigned int_key_hash(void* key)
//@ requires [?f]int_k_p(key, ?k);
//@ ensures [f]int_k_p(key, k) &*& result == int_hash(k);
{
  struct int_key* ik = key;

  unsigned long long hash = ik->int_src_port;
  hash *= 31;

  hash += ik->dst_port;
  hash *= 31;

  hash += ik->int_src_ip;
  hash *= 31;

  hash += ik->dst_ip;
  hash *= 31;

  hash += ik->int_device_id;
  hash *= 31;

  hash += ik->protocol;

  hash = wrap(hash);

  return (unsigned) hash;
}

unsigned ext_key_hash(void* key)
//@ requires [?f]ext_k_p(key, ?k);
//@ ensures [f]ext_k_p(key, k) &*& result == ext_hash(k);
{
  struct ext_key* ek = key;

  unsigned long long hash = ek->ext_src_port;
  hash *= 31;

  hash += ek->dst_port;
  hash *= 31;

  hash += ek->ext_src_ip;
  hash *= 31;

  hash += ek->dst_ip;
  hash *= 31;

  hash += ek->ext_device_id;
  hash *= 31;

  hash += ek->protocol;

  hash = wrap(hash);

  return (unsigned) hash;
}

//@ fixpoint bool my_offset(struct flow* fp, struct int_key* ik, struct ext_key* ek) { return &(fp->ik) == ik && &(fp->ek) == ek; }

/*@
  fixpoint bool flow_keys_offsets_fp1(struct flow* fp,
                                      struct int_key* ik,
                                      struct ext_key* ek) {
    return &(fp->ek) == ek;
  }


@*/

void flow_extract_keys(void* flwp, void** ikpp, void** ekpp)
//@ requires [?f]flw_p(flwp, ?flw) &*& *ikpp |-> _ &*& *ekpp |-> _;
/*@ ensures [f]flow_p(flwp, flw) &*& *ikpp |-> ?ikp &*& *ekpp |-> ?ekp &*&
            [f]int_k_p(ikp, ?ik) &*& [f]ext_k_p(ekp, ?ek) &*&
            true == flow_keys_offsets_fp(flwp, ikp, ekp) &*&
            ik == flw_get_ik(flw) &*& ek == flw_get_ek(flw); @*/
{
  //@ open [f]flw_p(flwp, flw);
  struct flow* fp = flwp;
  *ikpp = &fp->ik;
  *ekpp = &fp->ek;
  //@ close [f]flow_p(flwp, flw);
}

void flow_pack_keys(void* flwp, void* ikp, void* ekp)
/*@ requires [?f]flow_p(flwp, ?flw) &*&
             [f]int_k_p(ikp, ?ik) &*& [f]ext_k_p(ekp, ?ek) &*&
             true == flow_keys_offsets_fp(flwp, ikp, ekp) &*&
             ik == flw_get_ik(flw) &*& ek == flw_get_ek(flw); @*/
//@ ensures [f]flw_p(flwp, flw);
{
  IGNORE(flwp);
  IGNORE(ikp);
  IGNORE(ekp);
  //@ open flow_p(flwp, flw);
}

void flow_cpy(char* dst, void* src)
//@ requires [?fr]flw_p(src, ?f) &*& dst[0..sizeof(struct flow)] |-> _;
//@ ensures [fr]flw_p(src, f) &*& flw_p((void*)dst, f);
{
  struct flow* source = src;
  struct flow* destination = (void*)dst;
  //@ close_struct(destination);
  destination->ik.int_src_port = source->ik.int_src_port;
  destination->ik.dst_port = source->ik.dst_port;
  destination->ik.int_src_ip = source->ik.int_src_ip;
  destination->ik.dst_ip = source->ik.dst_ip;
  destination->ik.int_device_id = source->ik.int_device_id;
  destination->ik.protocol = source->ik.protocol;
  destination->ek.ext_src_port = source->ek.ext_src_port;
  destination->ek.dst_port = source->ek.dst_port;
  destination->ek.ext_src_ip = source->ek.ext_src_ip;
  destination->ek.dst_ip = source->ek.dst_ip;
  destination->ek.ext_device_id = source->ek.ext_device_id;
  destination->ek.protocol = source->ek.protocol;
  destination->int_src_port = source->int_src_port;
  destination->ext_src_port = source->ext_src_port;
  destination->dst_port = source->dst_port;
  destination->int_src_ip = source->int_src_ip;
  destination->ext_src_ip = source->ext_src_ip;
  destination->dst_ip = source->dst_ip;
  destination->int_device_id = source->int_device_id;
  destination->ext_device_id = source->ext_device_id;
  destination->protocol = source->protocol;
}

void flow_destroy(void* flwp)
//@ requires flw_p(flwp, ?flw);
//@ ensures chars(flwp, sizeof(struct flow), _);
{
  IGNORE(flwp);
  //do nothing
  //@ open flw_p(flwp, _);
  //@ open_struct((struct flow*)flwp);
}

#ifdef KLEE_VERIFICATION

struct str_field_descr int_key_descrs[] = {
  {offsetof(struct int_key, int_src_port), sizeof(uint16_t), "int_src_port"},
  {offsetof(struct int_key, dst_port), sizeof(uint16_t), "dst_port"},
  {offsetof(struct int_key, int_src_ip), sizeof(uint32_t), "int_src_ip"},
  {offsetof(struct int_key, dst_ip), sizeof(uint32_t), "dst_ip"},
  {offsetof(struct int_key, int_device_id), sizeof(uint16_t), "int_device_id"},
  {offsetof(struct int_key, protocol), sizeof(uint8_t), "protocol"},
};
struct str_field_descr ext_key_descrs[] = {
  {offsetof(struct ext_key, ext_src_port), sizeof(uint16_t), "ext_src_port"},
  {offsetof(struct ext_key, dst_port), sizeof(uint16_t), "dst_port"},
  {offsetof(struct ext_key, ext_src_ip), sizeof(uint32_t), "ext_src_ip"},
  {offsetof(struct ext_key, dst_ip), sizeof(uint32_t), "dst_ip"},
  {offsetof(struct ext_key, ext_device_id), sizeof(uint16_t), "ext_device_id"},
  {offsetof(struct ext_key, protocol), sizeof(uint8_t), "protocol"},
};
struct nested_field_descr flow_nests[] = {
  {offsetof(struct flow, ik), offsetof(struct int_key, int_src_port),
   sizeof(uint16_t), "int_src_port"},
  {offsetof(struct flow, ik), offsetof(struct int_key, dst_port),
   sizeof(uint16_t), "dst_port"},
  {offsetof(struct flow, ik), offsetof(struct int_key, int_src_ip),
   sizeof(uint32_t), "int_src_ip"},
  {offsetof(struct flow, ik), offsetof(struct int_key, dst_ip),
   sizeof(uint32_t), "dst_ip"},
  {offsetof(struct flow, ik), offsetof(struct int_key, int_device_id),
   sizeof(uint16_t), "int_device_id"},
  {offsetof(struct flow, ik), offsetof(struct int_key, protocol),
   sizeof(uint8_t), "protocol"},

  {offsetof(struct flow, ek), offsetof(struct ext_key, ext_src_port),
   sizeof(uint16_t), "ext_src_port"},
  {offsetof(struct flow, ek), offsetof(struct ext_key, dst_port),
   sizeof(uint16_t), "dst_port"},
  {offsetof(struct flow, ek), offsetof(struct ext_key, ext_src_ip),
   sizeof(uint32_t), "ext_src_ip"},
  {offsetof(struct flow, ek), offsetof(struct ext_key, dst_ip),
   sizeof(uint32_t), "dst_ip"},
  {offsetof(struct flow, ek), offsetof(struct ext_key, ext_device_id),
   sizeof(uint16_t), "ext_device_id"},
  {offsetof(struct flow, ek), offsetof(struct ext_key, protocol),
   sizeof(uint8_t), "protocol"},
};

struct str_field_descr flow_descrs[] = {
  {offsetof(struct flow, ik), sizeof(struct int_key), "ik"},
  {offsetof(struct flow, ek), sizeof(struct ext_key), "ek"},
  {offsetof(struct flow, int_src_port), sizeof(uint16_t), "int_src_port"},
  {offsetof(struct flow, ext_src_port), sizeof(uint16_t), "ext_src_port"},
  {offsetof(struct flow, dst_port), sizeof(uint16_t), "dst_port"},
  {offsetof(struct flow, int_src_ip), sizeof(uint32_t), "int_src_ip"},
  {offsetof(struct flow, ext_src_ip), sizeof(uint32_t), "ext_src_ip"},
  {offsetof(struct flow, dst_ip), sizeof(uint32_t), "dst_ip"},
  {offsetof(struct flow, int_device_id), sizeof(uint16_t), "int_device_id"},
  {offsetof(struct flow, ext_device_id), sizeof(uint16_t), "ext_device_id"},
  {offsetof(struct flow, protocol), sizeof(uint8_t), "protocol"},
};

int flow_consistency(void* key_a, void* key_b,
                     int index, void* value) {
  struct int_key* int_key = key_a;
  struct ext_key* ext_key = key_b;
  struct flow* flow = value;
  return
#if 0 //Semantics - inessential for the crash-freedom.
    ( int_key->int_src_port == flow->int_src_port ) &
    ( int_key->dst_port == flow->dst_port ) &
    ( int_key->int_src_ip == flow->int_src_ip ) &
    ( int_key->dst_ip == flow->dst_ip ) &
    ( int_key->int_device_id == flow->int_device_id ) &
    ( int_key->protocol == flow->protocol ) &

    ( int_key->int_src_port == flow->ik.int_src_port ) &
    ( int_key->dst_port == flow->ik.dst_port ) &
    ( int_key->int_src_ip == flow->ik.int_src_ip ) &
    ( int_key->dst_ip == flow->ik.dst_ip ) &
    ( int_key->int_device_id == flow->ik.int_device_id ) &
    ( int_key->protocol == flow->ik.protocol ) &

    //(0 == memcmp(int_key, &flow->ik, sizeof(struct int_key))) &
    ( ext_key->ext_src_port == flow->ext_src_port ) &
    ( ext_key->dst_port == flow->dst_port ) &
    ( ext_key->ext_src_ip == flow->ext_src_ip ) &
    ( ext_key->dst_ip == flow->dst_ip ) &
    ( ext_key->ext_device_id == flow->ext_device_id ) &
    ( ext_key->protocol == flow->protocol ) &

    ( ext_key->ext_src_port == flow->ek.ext_src_port ) &
    ( ext_key->dst_port == flow->ek.dst_port ) &
    ( ext_key->ext_src_ip == flow->ek.ext_src_ip ) &
    ( ext_key->dst_ip == flow->ek.dst_ip ) &
    ( ext_key->ext_device_id == flow->ek.ext_device_id ) &
    ( ext_key->protocol == flow->ek.protocol ) &
#endif//0 -- inessential for crash freedom part.
    ( 0 <= flow->int_device_id ) &
          ( flow->int_device_id < RTE_MAX_ETHPORTS ) &
    ( 0 <= flow->ext_device_id ) & //FIXME: Klee translates this to signed variable
          (flow->ext_device_id < RTE_MAX_ETHPORTS ) &
    ( ext_key->ext_device_id == flow->ek.ext_device_id ) &
    ( ext_key->ext_device_id == flow->ext_device_id ) &
    ( int_key->int_device_id == flow->ik.int_device_id ) &
    ( int_key->int_device_id == flow->int_device_id ) &
    ( flow->int_device_id != flow->ext_device_id ) &
    ( ext_key->ext_src_port == GLOBAL_starting_port + index ) &
    ( flow->ext_src_port == GLOBAL_starting_port + index ) &
    ( flow->ek.ext_src_port == GLOBAL_starting_port + index );
    //(0 == memcmp(ext_key, &flow->ek, sizeof(struct ext_key)));
}
#endif//KLEE_VERIFICATION

#ifdef ENABLE_LOG
#include "lib/nf_log.h"
#include <rte_byteorder.h>

void log_ip(uint32_t addr) {
  NF_DEBUG( "%d.%d.%d.%d",
            addr&0xff, (addr>>8)&0xff,
            (addr>>16)&0xff, (addr>>24)&0xff);
}

void log_int_key(const struct int_key *key) {
  NF_DEBUG( "{int_src_port: %d(%d); dst_port: %d(%d);\n"
            " int_src_ip: ",
            key->int_src_port, rte_be_to_cpu_16(key->int_src_port),
            key->dst_port, rte_be_to_cpu_16(key->dst_port));
  log_ip(key->int_src_ip);
  NF_DEBUG( "; dst_ip: ");
  log_ip(key->dst_ip);
  NF_DEBUG(" int_device_id: %d; protocol: %d}",
           key->int_device_id, key->protocol);
}

void log_ext_key(const struct ext_key *key) {
  NF_DEBUG( "{ext_src_port: %d(%d); dst_port: %d(%d);\n"
            " ext_src_ip: ",
            key->ext_src_port, rte_be_to_cpu_16(key->ext_src_port),
            key->dst_port, rte_be_to_cpu_16(key->dst_port));
  log_ip(key->ext_src_ip);
  NF_DEBUG( "; dst_ip: ");
  log_ip(key->dst_ip);
  NF_DEBUG(" ext_device_id: %d; protocol: %d}",
           key->ext_device_id, key->protocol);
}

void log_flow(const struct flow *f) {
  NF_DEBUG( "{int_src_port: %d(%d); ext_src_port: %d(%d);\n"
            " dst_port: %d(%d); int_src_ip: ",
            f->int_src_port, rte_be_to_cpu_16(f->int_src_port),
            f->ext_src_port, rte_be_to_cpu_16(f->ext_src_port),
            f->dst_port, rte_be_to_cpu_16(f->dst_port));
  log_ip(f->int_src_ip);
  NF_DEBUG( ";\n ext_src_ip:");
  log_ip(f->ext_src_ip);
  NF_DEBUG( "; dst_ip: ");
  log_ip(f->dst_ip);
  NF_DEBUG( " int_device_id: %d; ext_device_id: %d;\n"
            " protocol: %d}",
            f->int_device_id, f->ext_device_id, f->protocol);
}
#else
void log_ip(uint32_t addr) {
	IGNORE(addr);
}

void log_int_key(const struct int_key* key) {
	IGNORE(key);
}

void log_ext_key(const struct ext_key* key) {
	IGNORE(key);
}

void log_flow(const struct flow* f) {
	IGNORE(f);
}
#endif
