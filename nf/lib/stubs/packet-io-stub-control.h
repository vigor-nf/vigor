#ifndef _PACKET_IO_STUB_CONTROL_H_INCLUDED_
#define _PACKET_IO_STUB_CONTROL_H_INCLUDED_
#include "lib/stubs/containers/str-descr.h"

void packet_set_next_chunk_layout(struct Packet* p, uint32_t length,
                                  struct str_field_descr* fields, int n_fields,
                                  struct nested_field_descr* nests, int n_nests,
                                  const char* tname);

#endif//_PACKET_IO_STUB_CONTROL_H_INCLUDED_
