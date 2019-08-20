#ifndef _PACKET_IO_STUB_CONTROL_H_INCLUDED_
#define _PACKET_IO_STUB_CONTROL_H_INCLUDED_
#include "libvig/stubs/containers/str-descr.h"

typedef bool (*chunk_constraint)(void *);

void set_packet_receive_success(bool received);

void packet_set_next_chunk_layout(void *p, uint32_t length,
                                  struct str_field_descr *fields, int n_fields,
                                  struct nested_field_descr *nests, int n_nests,
                                  const char *tname);

bool packet_is_last_borrowed_chunk(void *p, void *chunk);

#endif //_PACKET_IO_STUB_CONTROL_H_INCLUDED_
