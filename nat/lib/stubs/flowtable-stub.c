#include <assert.h>
#include <klee/klee.h>
#include "lib/flowtable.h"
#include "my-time-stub-control.h"

#define LOG(...)

struct like_hash {
    struct flow sample_flow;//Contains both keys.
    int sample_initialized;
    int has_next_key;
    int allocated_index;
} like_hash;

int successfully_allocated = 0;

static inline void fill_int_key(struct flow *f, struct int_key *k) {
    k->int_src_port = f->int_src_port;
    k->dst_port = f->dst_port;
    k->int_src_ip = f->int_src_ip;
    k->dst_ip = f->dst_ip;
    k->int_device_id = f->int_device_id;
    k->protocol = f->protocol;
}

static inline void fill_ext_key(struct flow *f, struct ext_key *k) {
    k->ext_src_port = f->ext_src_port;
    k->dst_port = f->dst_port;
    k->ext_src_ip = f->ext_src_ip;
    k->dst_ip = f->dst_ip;
    k->ext_device_id = f->ext_device_id;
    k->protocol = f->protocol;
}

int get_flow_int(struct int_key* key, int* index) {
    klee_assert(successfully_allocated);
    LOG("look up for internal key key = \n");
    log_int_key(key);
    if (like_hash.has_next_key) {
        klee_assert(!like_hash.sample_initialized);
        like_hash.sample_flow.ik = *key;

        like_hash.sample_flow.int_src_port = key->int_src_port;
        like_hash.sample_flow.dst_port = key->dst_port;
        like_hash.sample_flow.int_src_ip = key->int_src_ip;
        like_hash.sample_flow.dst_ip = key->dst_ip;
        like_hash.sample_flow.int_device_id = key->int_device_id;
        like_hash.sample_flow.protocol = key->protocol;

        fill_ext_key(&like_hash.sample_flow, &like_hash.sample_flow.ek);

	LOG("HT entry is allocated on int\n");
        like_hash.sample_initialized = 1;
        *index = like_hash.allocated_index;
        return 1;
    } else {
        return 0;
    }
}

int get_flow_ext(struct ext_key* key, int* index) {
    klee_assert(successfully_allocated);
    if (like_hash.has_next_key) {
        klee_assert(!like_hash.sample_initialized);
        like_hash.sample_flow.ek = *key;

        like_hash.sample_flow.ext_src_port = key->ext_src_port;
        like_hash.sample_flow.dst_port = key->dst_port;
        like_hash.sample_flow.ext_src_ip = key->ext_src_ip;
        like_hash.sample_flow.dst_ip = key->dst_ip;
        like_hash.sample_flow.ext_device_id = key->ext_device_id;
        like_hash.sample_flow.protocol = key->protocol;

        fill_int_key(&like_hash.sample_flow, &like_hash.sample_flow.ik);

	LOG("HT entry is allocated on ext\n");
        like_hash.sample_initialized = 1;
        *index = like_hash.allocated_index;
        return 1;
    } else {
        return 0;
    }
}

struct flow* get_flow(int index) {
    klee_assert(successfully_allocated);
    klee_assert(index == like_hash.allocated_index);
    klee_assert(like_hash.sample_initialized);
    return &like_hash.sample_flow;
}

int add_flow(struct flow *f, int index) {
    klee_assert(successfully_allocated);
    LOG("add_flow (f = \n");
    log_flow(f);

    klee_assert(!like_hash.sample_initialized);

    like_hash.sample_flow = *f;
    fill_int_key(f, &like_hash.sample_flow.ik);
    fill_ext_key(f, &like_hash.sample_flow.ek);

    like_hash.sample_initialized = 1;
    like_hash.allocated_index = index;
    LOG("HT entry is allocated on explicit add\n");
    return 1;
    // It can not ever return 0. To be verified.
}

int remove_flow(int index) {
    klee_assert(successfully_allocated);
    klee_assert(0); // This model does not support removal.
    return 1;
}

int allocate_flowtables(uint8_t nb_ports) {
    successfully_allocated = klee_int("flowtables_successfully_allocated");
    if (successfully_allocated) {
        klee_make_symbolic(&like_hash, sizeof(struct like_hash), "like_hash");

        fill_int_key(&like_hash.sample_flow, &like_hash.sample_flow.ik);
        fill_ext_key(&like_hash.sample_flow, &like_hash.sample_flow.ek);

        klee_assume(like_hash.sample_flow.int_device_id < nb_ports);
        klee_assume(like_hash.sample_flow.ext_device_id < nb_ports);
        klee_assume(like_hash.sample_initialized == 0);
        klee_assume(0 <= like_hash.allocated_index);
        klee_assume(like_hash.allocated_index < MAX_FLOWS);
        klee_assume(like_hash.sample_flow.timestamp < get_start_time());
        return 1;
    }
    return 0;
}
