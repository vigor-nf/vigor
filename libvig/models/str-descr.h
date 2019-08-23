#ifndef _STR_DESCR_H_INCLUDED_
#define _STR_DESCR_H_INCLUDED_

// This file is not a model itself, but a definition of types used in models

struct str_field_descr {
  int offset;
  int width;
  int count;
  char *name;
};

struct nested_field_descr {
  int base_offset;
  int offset;
  int width;
  int count;
  char *name;
};

struct nested_nested_field_descr {
  int base_base_offset;
  int base_offset;
  int offset;
  int width;
  char *name;
};

#endif //_STR_DESCR_H_INCLUDED_
