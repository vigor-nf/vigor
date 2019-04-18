#include "lib/expirator.h"
#include "lib/stubs/time_stub_control.h"
#include "lib/containers/map.h"
#include "lib/containers/double-chain.h"
#include "vigbalancer/lb_loop.h"
#include <stdint.h>
#include <stdbool.h>
#include <string.h>
#include "lib/stubs/core_stub.h"
#include "lib/containers/emap.h"
#include "lib/packet-io.h"
#include "lib/packet-headers.h"

// VeriFast can't deal with bitwise AND, so we hardcode known cases.
/*@
lemma void bit_and_hack()
requires true;
ensures 0x00 == (0x00 & 0x10) 
    &*& 0x00 == (0x01 & 0x10)
    &*& 0x10 == (0x11 & 0x10)
    &*& 0x00 == (0x41 & 0x10)
    &*& 0x10 == (0x111 & 0x10)
    &*& 0x10 == (0x211 & 0x10)
    &*& 0x00 == (0x241 & 0x10);
{
  assume(false);
}

lemma_auto void bit_and_equiv(unsigned int i)
requires i < 65536;
ensures i == (i & 65535);
{
  assume(false);
}

// VeriFast can't reason about modulo either, let's help it a bit...
lemma void modulo_hack()
requires true;
ensures forall_(int i; i < 0 || i % 2 == 0 || i % 2 == 1);
{
  assume(false);
}
@*/

void umemcpy(void *array, void *array0, size_t count);
    //@ requires uchars(array, count, ?cs) &*& [?f]uchars(array0, count, ?cs0);
    //@ ensures uchars(array, count, cs0) &*& [f]uchars(array0, count, cs0);
/*@ predicate hide_is_map_keys_equality<t>(map_keys_equality* fun,
                                           predicate (void*;t) keyp) =
      is_map_keys_equality<t>(fun, keyp);
 @*/

/*@ predicate hide_is_map_key_hash<t>(map_key_hash* fun,
                                      predicate (void*;t) keyp,
                                      fixpoint (t,int) hsh) =
      is_map_key_hash<t>(fun, keyp, hsh);
 @*/

/*@ predicate hide_mapp<t>(struct Map* p,
                           predicate (void*;t) kp,
                           fixpoint (t,int) hsh,
                           fixpoint (t,int,bool) recp,
                           mapi<t> m) = mapp<t>(p, kp, hsh, recp, m); @*/

/*@ predicate hide_vector<t>(struct Vector* vector,
                             predicate (void*;t) entp,
                             list<pair<t, real> > values,
                             list<void*> addrs) = vectorp<t>(vector, entp, values, addrs); @*/
enum LMA_enum {LMA_LOADBALANCEDFLOW, LMA_IP_ADDR, LMA_INVALID};
void to_verify()
/*@ requires true; @*/ 
/*@ ensures true; @*/
{
uint16_t received_on_port;
int the_index_allocated = -1;
int64_t time_for_allocated_index = 0;
bool a_packet_received = false;
//@ list<pair<LoadBalancedFlowi, int> > initial_flow_to_flow_id;
//@ struct Map* flow_to_flow_id_ptr;
//@ list<pair<LoadBalancedFlowi, real> > initial_flow_heap;
//@ struct Vector* flow_heap_ptr;
//@ dchain initial_flow_chain;
//@ struct DoubleChain* flow_chain_ptr;
//@ list<pair<uint32_t, real> > initial_flow_id_to_backend_id;
//@ struct Vector* flow_id_to_backend_id_ptr;
//@ list<pair<ip_addri, int> > initial_ip_to_backend_id;
//@ struct Map* ip_to_backend_id_ptr;
//@ list<pair<ip_addri, real> > initial_backend_ips;
//@ struct Vector* backend_ips_ptr;
//@ list<pair<LoadBalancedBackendi, real> > initial_backends;
//@ struct Vector* backends_ptr;
//@ dchain initial_active_backends;
//@ struct DoubleChain* active_backends_ptr;
//@ list<pair<uint32_t, real> > initial_cht;
//@ struct Vector* cht_ptr;
//@ int backend_capacity;
//@ int flow_capacity;
//@ int cht_height;
//@ option<void*> last_composed_packet = none;
//@ bool packet_is_complete = false;
//@ list<uint8_t> last_sent_packet = nil;
//@ list<phdr> recv_headers = nil; 
//@ list<phdr> sent_headers = nil; 
//@ list<uint16_t> sent_on_ports = nil; 
//@ assume(sizeof(struct ether_hdr) == 14);
//@ assume(sizeof(struct tcpudp_hdr) == 4);
//@ assume(sizeof(struct ipv4_hdr) == 20);//TODO: handle all this sizeof's explicitly
int vector_allocation_order = 0;
int map_allocation_order = 0;
int dchain_allocation_order = 0;
int expire_items_single_map_order = 0;
enum LMA_enum last_map_accessed = LMA_LOADBALANCEDFLOW;
//@ LoadBalancedFlowi last_LoadBalancedFlow_searched_in_the_map;
//@ ip_addri last_ip_addr_searched_in_the_map;


struct Map* arg1;
struct Vector* arg2;
struct DoubleChain* arg3;
struct Vector* arg4;
struct Vector* arg5;
struct Map* arg1bis;
struct Vector* arg2bis;
struct DoubleChain* arg3bis;
struct Vector* arg4bis;
struct Vector* arg5bis;
arg1 = arg1bis;
*(&(arg1)) = arg1bis;
arg2 = arg2bis;
*(&(arg2)) = arg2bis;
arg3 = arg3bis;
*(&(arg3)) = arg3bis;
arg4 = arg4bis;
*(&(arg4)) = arg4bis;
arg5 = arg5bis;
*(&(arg5)) = arg5bis;
//@ assume(arg1 == arg1bis);
//@ assume(arg2 == arg2bis);
//@ assume(arg3 == arg3bis);
//@ assume(arg4 == arg4bis);
//@ assume(arg5 == arg5bis);

arg4 = (struct Vector*)0;// PRECONDITIONS
*(&(arg1)) = (struct Map*)0;// PRELEMMAS AND CALL
/*@ 
switch(map_allocation_order) {
 case 0:
produce_function_pointer_chunk map_keys_equality<LoadBalancedFlowi>(LoadBalancedFlow_eq)(LoadBalancedFlowp)(a, b) {call();}
produce_function_pointer_chunk map_key_hash<LoadBalancedFlowi>(LoadBalancedFlow_hash)(LoadBalancedFlowp, _LoadBalancedFlow_hash)(a) {call();}

              break;
 case 1:
produce_function_pointer_chunk map_keys_equality<ip_addri>(ip_addr_eq)(ip_addrp)(a, b) {call();}
produce_function_pointer_chunk map_key_hash<ip_addri>(ip_addr_hash)(ip_addrp, _ip_addr_hash)(a) {call();}

              break;
default:
assert false;
}
 @*/
int32_t ret0 = map_allocate(LoadBalancedFlow_eq, LoadBalancedFlow_hash, 65536, &(arg1));
// RET STUFF
//@ assume(ret0 == 1);

// POSTLEMMAS
/*@ 
switch(map_allocation_order) {
 case 0:
assert [?imkest0]is_map_keys_equality(LoadBalancedFlow_eq,LoadBalancedFlowp);
close [imkest0]hide_is_map_keys_equality(LoadBalancedFlow_eq, LoadBalancedFlowp);
assert [?imkhst0]is_map_key_hash(LoadBalancedFlow_hash,LoadBalancedFlowp, _LoadBalancedFlow_hash);
close [imkhst0]hide_is_map_key_hash(LoadBalancedFlow_hash, LoadBalancedFlowp, _LoadBalancedFlow_hash);
break;
 case 1:
assert [?imkest0]is_map_keys_equality(ip_addr_eq,ip_addrp);
close [imkest0]hide_is_map_keys_equality(ip_addr_eq, ip_addrp);
assert [?imkhst0]is_map_key_hash(ip_addr_hash,ip_addrp, _ip_addr_hash);
close [imkhst0]hide_is_map_key_hash(ip_addr_hash, ip_addrp, _ip_addr_hash);
break;
default:
assert false;
}
 @*/
map_allocation_order += 1;
// POSTCONDITIONS



// PRECONDITIONS
*(&(arg2)) = (struct Vector*)0;// PRELEMMAS AND CALL
/*@ 
switch(vector_allocation_order) {
 case 0:
produce_function_pointer_chunk vector_init_elem<LoadBalancedFlowi>(LoadBalancedFlow_allocate)(LoadBalancedFlowp, sizeof(struct LoadBalancedFlow))(a) {call();}
break;
 case 1:
produce_function_pointer_chunk vector_init_elem<uint32_t>(null_init)(u_integer, sizeof(uint32_t))(a) {call();}
break;
 case 2:
produce_function_pointer_chunk vector_init_elem<ip_addri>(ip_addr_allocate)(ip_addrp, sizeof(struct ip_addr))(a) {call();}
break;
 case 3:
produce_function_pointer_chunk vector_init_elem<LoadBalancedBackendi>(LoadBalancedBackend_allocate)(LoadBalancedBackendp, sizeof(struct LoadBalancedBackend))(a) {call();}
break;
 case 4:
produce_function_pointer_chunk vector_init_elem<uint32_t>(null_init)(u_integer, sizeof(uint32_t))(a) {call();}
break;
default:
assert false;
}
 @*/

switch(vector_allocation_order) {
 case 0:
//@assume(sizeof(struct LoadBalancedFlow) == 16);
break;
 case 1:
//@assume(sizeof(uint32_t) == 16);
break;
 case 2:
//@assume(sizeof(struct ip_addr) == 16);
break;
 case 3:
//@assume(sizeof(struct LoadBalancedBackend) == 16);
break;
 case 4:
//@assume(sizeof(uint32_t) == 16);
break;
default:
assert false;
}

int32_t ret1 = vector_allocate(16, 65536, LoadBalancedFlow_allocate, &(arg2));
// RET STUFF
//@ assume(ret1 == 1);

// POSTLEMMAS

switch(vector_allocation_order) {
 case 0:
/*@ if (ret1) {
assert mapp<LoadBalancedFlowi>(_, _, _, _, mapc(?cap1, ?map1, ?addr_map1));
assert vectorp<LoadBalancedFlowi>(_, _, ?dks1, ?dkaddrs1);
empty_kkeeper(dkaddrs1, dks1, addr_map1, cap1);
}@*/break;
 case 1:
break;
 case 2:
/*@ if (ret1) {
assert mapp<ip_addri>(_, _, _, _, mapc(?cap1, ?map1, ?addr_map1));
assert vectorp<ip_addri>(_, _, ?dks1, ?dkaddrs1);
empty_kkeeper(dkaddrs1, dks1, addr_map1, cap1);
}@*/break;
 case 3:
break;
 case 4:
break;
default:
assert false;
}

vector_allocation_order += 1;
// POSTCONDITIONS



// PRECONDITIONS
// PRELEMMAS AND CALL

int32_t ret2 = dchain_allocate(65536, &(arg3));
// RET STUFF
//@ assume(ret2 == 1);

// POSTLEMMAS
switch(dchain_allocation_order) {
 case 0:
//@ index_range_of_empty(65536, 0);
/*@ if (ret2 != 0) {
assert vectorp<LoadBalancedFlowi>(_, _, ?allocated_vector, _);
empty_map_vec_dchain_coherent<LoadBalancedFlowi>(allocated_vector);
} @*/
break;
 case 1:
//@ index_range_of_empty(65536, 0);
/*@ if (ret2 != 0) {
assert vectorp<ip_addri>(_, _, ?allocated_vector, _);
empty_map_vec_dchain_coherent<ip_addri>(allocated_vector);
} @*/
break;
default:
assert false;
}
dchain_allocation_order += 1;
// POSTCONDITIONS



// No semantic checks for this trace
*(&(arg4)) = (struct Vector*)0;
/*@ 
switch(vector_allocation_order) {
 case 0:
produce_function_pointer_chunk vector_init_elem<LoadBalancedFlowi>(LoadBalancedFlow_allocate)(LoadBalancedFlowp, sizeof(struct LoadBalancedFlow))(a) {call();}
break;
 case 1:
produce_function_pointer_chunk vector_init_elem<uint32_t>(null_init)(u_integer, sizeof(uint32_t))(a) {call();}
break;
 case 2:
produce_function_pointer_chunk vector_init_elem<ip_addri>(ip_addr_allocate)(ip_addrp, sizeof(struct ip_addr))(a) {call();}
break;
 case 3:
produce_function_pointer_chunk vector_init_elem<LoadBalancedBackendi>(LoadBalancedBackend_allocate)(LoadBalancedBackendp, sizeof(struct LoadBalancedBackend))(a) {call();}
break;
 case 4:
produce_function_pointer_chunk vector_init_elem<uint32_t>(null_init)(u_integer, sizeof(uint32_t))(a) {call();}
break;
default:
assert false;
}
 @*/

switch(vector_allocation_order) {
 case 0:
//@assume(sizeof(struct LoadBalancedFlow) == 4);
break;
 case 1:
//@assume(sizeof(uint32_t) == 4);
break;
 case 2:
//@assume(sizeof(struct ip_addr) == 4);
break;
 case 3:
//@assume(sizeof(struct LoadBalancedBackend) == 4);
break;
 case 4:
//@assume(sizeof(uint32_t) == 4);
break;
default:
assert false;
}

int32_t ret3 = vector_allocate(4, 65536, null_init, &(arg4));

switch(vector_allocation_order) {
 case 0:
/*@ if (ret3) {
assert mapp<LoadBalancedFlowi>(_, _, _, _, mapc(?captip, ?maptip, ?addr_maptip));
assert vectorp<LoadBalancedFlowi>(_, _, ?dkstip, ?dkaddrstip);
empty_kkeeper(dkaddrstip, dkstip, addr_maptip, captip);
}@*/break;
 case 1:
break;
 case 2:
/*@ if (ret3) {
assert mapp<ip_addri>(_, _, _, _, mapc(?captip, ?maptip, ?addr_maptip));
assert vectorp<ip_addri>(_, _, ?dkstip, ?dkaddrstip);
empty_kkeeper(dkaddrstip, dkstip, addr_maptip, captip);
}@*/break;
 case 3:
break;
 case 4:
break;
default:
assert false;
}

vector_allocation_order += 1;
int export_point;
//@ assume(false);
}
