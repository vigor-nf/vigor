#ifndef _MAP_STUB_CONTROL_H_INCLUDED_
#define _MAP_STUB_CONTROL_H_INCLUDED_

#include "libvig/verified/map.h"
#include "libvig/models/str-descr.h"

#include <stdbool.h>

#define PREALLOC_SIZE (256)
#define NUM_ELEMS (3)

typedef bool map_entry_condition(void *key, int value, void* state);

struct Map {
  void *keyp[NUM_ELEMS];
  void *key_copyp[NUM_ELEMS];
  char key_copies[NUM_ELEMS * PREALLOC_SIZE];
  int unallocated_start;
  int allocated_index[NUM_ELEMS];
  int key_deleted[NUM_ELEMS];
  int next_unclaimed_entry;
  int capacity;
  int occupancy;
  int backup_occupancy;
  int has_layout;
  int key_size;
  int key_field_count;
  int nested_key_field_count;
  map_entry_condition *ent_cond;
  void *ent_cond_state;
  struct str_field_descr key_fields[PREALLOC_SIZE];
  struct nested_field_descr key_nests[PREALLOC_SIZE];
  char *key_type;
  map_keys_equality *keq;

  int Num_bucket_traversals;
  int Num_hash_collisions;
};

void map_set_layout(struct Map *map, struct str_field_descr *key_fields,
                    int key_fields_count, struct nested_field_descr *key_nests,
                    int nested_key_fields_count, char *key_type);

void map_set_entry_condition(struct Map *map, map_entry_condition *cond,
                             void* state);

void map_reset(struct Map *map);

#endif //_MAP_STUB_CONTROL_H_INCLUDED_
