open Data_spec

(* ===
  This file describes the NF state that persists the entire
  runtime of the NF.
  It defines two lists: `containers` and `custom_includes`.
  `containers` declare the persistent state of the NF,
  `custom_includes` lists the header files that contain
  definitions of user data records (C structs) together
  with anciliary functions such as eq or hash.
  These files are generated automatically based only on
  the C struct declaration. Hence the `.gen.h` suffix.
   === *)

(* ===
  `containers` lists all the data structures and simple values
  the NF uses to keep its persistent state.
  List items are pairs, separated by semicolons (;).
  Each pair contains the name of the variable, a string, followed by a comma
  and by specification of the type of that variable.
  Currently the variable may be of one of the following types:
  - integer type, like UInt32
  - map type (a dictionary with keys <record name>) with the specification:
          Map (<record name>, <capacity>, <record predicate>)
  - vector type (an array of <record name>) with the following specification:
          Vector (<record name>, <capacity>, <record predicate>)
  - DChain type (an expiring number allocator, think port allocator):
          Dchain <capacity>
  - CHT type (consistent hashing table):
          CHT (<capacity>, <height>)
  - expiring map type (a composition of a simple map (keys -> ints),
                       a vector (ints -> keys) used to store the keys
                       using the value associated in the map as an index,
                       and an expiring number allocator used
                       for indices in the vector (which are also the
                       associated values in the map))
          EMap (<record type>, <map>, <vector>, <dchain>)
   === *)
let containers = ["example_value", UInt32;]

(* ===
  `custom_includes` lists all the headers that declare the data records
  used in the NF state.
  These headers are generated automatically from the simple C struct declarations.
  e.g. "flow.h" with
  struct flow_id {
    uint16_t src_port;
    uint16_t dst_port;
    uint32_t src_ip;
    uint32_t dst_ip;
    uint8_t protocol;
  };
  yelds "flow.h.gen.h" with the comparison operator, hash function,
  allocation function, log function that are requried by
  libVig data structures.
   === *)
let custom_includes = ["flow.h.gen.h"]
