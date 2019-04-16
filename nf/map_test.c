#include <stdio.h>
#include <stdlib.h>
#include "lib/containers/map-impl.h"
#include "lib/containers/map.h"
#include "flow.h"
#include <limits.h>
#include <inttypes.h>
#include <time.h>
#include <assert.h>
#include <x86intrin.h>
#define capacity 65536
#define max_size 41943040

long long* a;
struct timespec gNeverZero;

static long long wrap2(long long x)
//@ requires true;
//@ ensures result == _wrap(x) &*& INT_MIN <= result &*& result <= INT_MAX;
{
  //@ div_rem(x, INT_MAX);
  return x % INT_MAX;
}

static int int_key_hash2(void* key)
//@ requires [?f]int_k_p(key, ?k);
//@ ensures [f]int_k_p(key, k) &*& result == int_hash(k);
{
  struct int_key* ik = key;

  long long hash = ik->int_src_port;
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

  hash = wrap2(hash);
  //if(gNeverZero.tv_nsec==0)
  	return (int) hash;
  // return ik ->int_src_port;
}

#define iterations 10000
#define flows 64000

void do_map_test(void)
{

 struct Map* map;
 map_allocate(int_key_eq,int_key_hash2,capacity,&map);
 struct int_key *k1 = malloc(sizeof(*k1)*capacity);
 long value,a,hash,erase_key ;
 int y,res;
 int* val = malloc(sizeof *val);
 void** b = malloc(sizeof(void*));
 struct int_key* k2 = malloc(sizeof *k2);

 int ret;

for (int i = 0; i < capacity; i++)
{
 k1[i].int_src_port = i;
 k1[i].dst_port =i;
 k1[i].int_src_ip = i;
 k1[i].dst_ip = i;
 k1[i].int_device_id = i;
 k1[i].protocol = i;
 value = 50*i;
}

  uint64_t start_time = __rdtsc();
for (uint64_t asdf = 0; asdf < (iterations); asdf++) {

  for (int i = 0; i < flows; i++)
  {
   map_put(map,&k1[i],value);
  }

  for (int i = 0; i < flows; i++)
  {
   map_erase(map,&k1[i],b);
  }

  // printf("asdf\n");
}
  uint64_t end_time = __rdtsc();
  printf("%" PRIu64 "\n", (end_time - start_time) / ((iterations) * flows));
}
