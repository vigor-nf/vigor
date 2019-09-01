#include <stdlib.h>
#include <string.h>
#include "klee/klee.h"
#include "libvig/verified/map.h"
#include "map-control.h"

#define PREALLOC_SIZE (256)

__attribute__((noinline)) int map_allocate(map_keys_equality *keq,
                                           map_key_hash *khash,
                                           unsigned capacity,
                                           struct Map **map_out) {
  klee_trace_ret();
  klee_trace_param_fptr(keq, "keq");
  klee_trace_param_fptr(khash, "khash");
  klee_trace_param_u32(capacity, "capacity");
  klee_trace_param_ptr(map_out, sizeof(struct Map *), "map_out");
  int allocation_succeeded = klee_int("map_allocation_succeeded");
  if (allocation_succeeded) {
    *map_out = malloc(sizeof(struct Map));
    klee_make_symbolic((*map_out), sizeof(struct Map), "map");
    klee_assert((*map_out) != NULL);
    for (int n = 0; n < NUM_ELEMS; ++n) {
      (*map_out)->keyp[n] = NULL;
      (*map_out)->key_copyp[n] = NULL;
      (*map_out)->key_deleted[n] = 0;
    }
    (*map_out)->unallocated_start = 0;
    (*map_out)->next_unclaimed_entry = 0;
    (*map_out)->keq = keq;
    (*map_out)->capacity = capacity;
    (*map_out)->has_layout = 0;
    (*map_out)->ent_cond = NULL;
    (*map_out)->ent_cond_state = NULL;
    (*map_out)->occupancy = klee_range(0, capacity, "map_occupancy");
    (*map_out)->backup_occupancy =
        klee_range(0, capacity, "backup_map_occupancy");
    (*map_out)->Num_bucket_traversals = klee_int("Num_bucket_traversals");
    (*map_out)->Num_hash_collisions = klee_int("Num_hash_collisions");
    return 1;
  }
  return 0;
}

void map_reset(struct Map *map) {
  // Do not trace. This function is an internal knob of the model.
  for (int n = 0; n < NUM_ELEMS; ++n) {
    map->keyp[n] = NULL;
    map->key_copyp[n] = NULL;
    map->key_deleted[n] = 0;
    map->allocated_index[n] = klee_int("map_allocated_index");
  }
  map->next_unclaimed_entry = 0;
  map->occupancy = map->backup_occupancy;
  map->unallocated_start = 0;
}

static int calculate_str_size(struct str_field_descr *descr, int len) {
  int rez = 0;
  int sum = 0;
  for (int i = 0; i < len; ++i) {
    sum += descr[i].width;
    if (descr[i].offset + descr[i].width > rez)
      rez = descr[i].offset + descr[i].width;
  }
  klee_assert(rez == sum);
  return rez;
}

void map_set_layout(struct Map *map, struct str_field_descr *key_fields,
                    int key_fields_count, struct nested_field_descr *key_nests,
                    int nested_key_fields_count, char *key_type) {
  // Do not trace. This function is an internal knob of the model.
  klee_assert(key_fields_count < PREALLOC_SIZE);
  klee_assert(nested_key_fields_count < PREALLOC_SIZE);
  memcpy(map->key_fields, key_fields,
         sizeof(struct str_field_descr) * key_fields_count);
  if (0 < nested_key_fields_count) {
    memcpy(map->key_nests, key_nests,
           sizeof(struct nested_field_descr) * nested_key_fields_count);
  }
  map->key_field_count = key_fields_count;
  map->nested_key_field_count = nested_key_fields_count;
  map->key_size = calculate_str_size(key_fields, key_fields_count);
  klee_assert(map->key_size < PREALLOC_SIZE);
  map->has_layout = 1;
  map->key_type = key_type;
}

void map_set_entry_condition(struct Map *map, map_entry_condition *cond,
                             void* cond_state) {
  map->ent_cond = cond;
  map->ent_cond_state = cond_state;
}

#define TRACE_KEY_FIELDS(key, map)                                             \
  {                                                                            \
    for (int i = 0; i < map->key_field_count; ++i) {                           \
      klee_trace_param_ptr_field_arr_directed(                                 \
          key, map->key_fields[i].offset, map->key_fields[i].width,            \
          map->key_fields[i].count, map->key_fields[i].name, TD_BOTH);         \
    }                                                                          \
    for (int i = 0; i < map->nested_key_field_count; ++i) {                    \
      klee_trace_param_ptr_nested_field_arr_directed(                          \
          key, map->key_nests[i].base_offset, map->key_nests[i].offset,        \
          map->key_nests[i].width, map->key_nests[i].count,                    \
          map->key_nests[i].name, TD_BOTH);                                    \
    }                                                                          \
  }

__attribute__((noinline)) int map_get(struct Map *map, void *key,
                                      int *value_out) {
  klee_trace_ret();
  klee_assert(map->has_layout);
  // To avoid symbolic-pointer-dereference,
  // consciously trace "map" as a simple value.
  klee_trace_param_i32((uint32_t)map, "map");

  klee_trace_param_tagged_ptr(key, map->key_size, "key", map->key_type,
                              TD_BOTH);
  klee_trace_param_ptr(value_out, sizeof(int), "value_out");
  TRACE_KEY_FIELDS(key, map);
  for (int n = 0; n < map->next_unclaimed_entry; ++n) {
    if (map->keq(key, map->key_copyp[n])) {
      if (map->key_deleted[n]) {
        return 0;
      } else {
        *value_out = map->allocated_index[n];
        return 1;
      }
    }
  }
  klee_assert(map->next_unclaimed_entry < NUM_ELEMS &&
              "No space left in the map stub");
  if (klee_int("map_has_this_key")) {
    int n = map->next_unclaimed_entry;
    ++map->next_unclaimed_entry;
    map->key_deleted[n] = 0;
    map->keyp[n] = key;
    map->key_copyp[n] = map->key_copies + map->unallocated_start;
    map->unallocated_start += map->key_size;
    memcpy(map->key_copyp[n], key, map->key_size);
    map->allocated_index[n] = klee_int("allocated_index");
    if (map->ent_cond) {
      klee_assume(map->ent_cond(map->keyp[n], map->allocated_index[n],
                                map->ent_cond_state));
      klee_assume(map->ent_cond(map->key_copyp[n], map->allocated_index[n],
                                map->ent_cond_state));
    }
    *value_out = map->allocated_index[n];
    return 1;
  } else {
    return 0;
  }
}

__attribute__((noinline)) void map_put(struct Map *map, void *key, int value) {
  klee_trace_ret();
  klee_assert(map->has_layout);
  // To avoid symbolic-pointer-dereference,
  // consciously trace "map" as a simple value.
  klee_trace_param_i32((uint32_t)map, "map");

  klee_trace_param_tagged_ptr(key, map->key_size, "key", map->key_type,
                              TD_BOTH);
  klee_trace_param_i32(value, "value");
  TRACE_KEY_FIELDS(key, map);
  if (map->ent_cond) {
    klee_assert(map->ent_cond(key, value, map->ent_cond_state));
  }
  map->occupancy += 1;
  for (int n = 0; n < map->next_unclaimed_entry; ++n) {
    if (map->keq(key, map->key_copyp[n])) {
      klee_assert(map->key_deleted[n] && "Duplicate key, otherwise");
      map->key_deleted[n] = 0;
      map->allocated_index[n] = value;
      return; // Undeleted a key -> like inserted one, no need for another one.
    }
  }
  klee_assert(map->next_unclaimed_entry < NUM_ELEMS &&
              "No space left in the map stub");
  int n = map->next_unclaimed_entry;
  ++map->next_unclaimed_entry;
  map->key_deleted[n] = 0;
  map->keyp[n] = key;
  map->key_copyp[n] = map->key_copies + map->unallocated_start;
  map->unallocated_start += map->key_size;
  memcpy(map->key_copyp[n], key, map->key_size);
  map->allocated_index[n] = value;
}

__attribute__((noinline)) void map_erase(struct Map *map, void *key,
                                         void **trash) {
  klee_trace_ret();
  klee_assert(map->has_layout);
  // To avoid symbolic-pointer-dereference,
  // consciously trace "map" as a simple value.
  klee_trace_param_i32((uint32_t)map, "map");

  klee_trace_param_tagged_ptr(key, map->key_size, "key", map->key_type,
                              TD_BOTH);
  TRACE_KEY_FIELDS(key, map);
  klee_trace_param_tagged_ptr(trash, sizeof(void *), "trash", map->key_type,
                              TD_OUT);

  map->occupancy -= 1;
  for (int n = 0; n < map->next_unclaimed_entry; ++n) {
    if (map->keq(key, map->key_copyp[n])) {
      // It is important to differentiate the case
      // when that the key was deleted from the map,
      // as opposed to never existed on the first place.
      map->key_deleted[n] = 1;
      return; // The key is deleted, job's done
    }
  }
  assert(map->next_unclaimed_entry < NUM_ELEMS &&
         "No more space in the map stub");
  // The key was not previously mentioned,
  // but we need to take a note that the key was deleted,
  // in case we access it in the future.
  int n = map->next_unclaimed_entry;
  ++map->next_unclaimed_entry;
  map->keyp[n] = key;
  map->key_copyp[n] = map->key_copies + map->unallocated_start;
  map->unallocated_start += map->key_size;
  memcpy(map->key_copyp[n], key, map->key_size);
  map->key_deleted[n] = 1;
}

__attribute__((noinline)) unsigned map_size(struct Map *map) {
  klee_trace_ret();
  // To avoid symbolic-pointer-dereference,
  // consciously trace "map" as a simple value.
  klee_trace_param_u64((uint64_t)map, "map");

  return klee_int("map_size");
}
