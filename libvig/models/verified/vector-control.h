#ifndef _VECTOR_STUB_CONTROL_H_INCLUDED_
#define _VECTOR_STUB_CONTROL_H_INCLUDED_

#include "libvig/verified/vector.h"
#include "libvig/models/str-descr.h"

#include <stdbool.h>

void vector_set_layout(struct Vector *vector,
                       struct str_field_descr *value_fields, int field_count,
                       struct nested_field_descr *val_nest_fields,
                       int nest_field_count, char *type_tag);

typedef bool vector_entry_condition(void *value, int index, void *state);

void vector_set_entry_condition(struct Vector *vector,
                                vector_entry_condition *cond, void *state);

void vector_reset(struct Vector *vector);

#endif // _VECTOR_STUB_CONTROL_H_INCLUDED_
