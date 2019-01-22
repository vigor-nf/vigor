#ifndef _PACKET_IO_STUB_CONTROL_H_INCLUDED_
#define _PACKET_IO_STUB_CONTROL_H_INCLUDED_
#include "lib/stubs/containers/str-descr.h"

typedef bool (*chunk_constraint)(void*);

void packet_set_next_chunk_layout(void* p, uint32_t length,
                                  struct str_field_descr* fields, int n_fields,
                                  struct nested_field_descr* nests, int n_nests,
                                  const char* tname);

void packet_set_next_chunk_constraints(void* p, chunk_constraint constraint);

#endif//_PACKET_IO_STUB_CONTROL_H_INCLUDED_
