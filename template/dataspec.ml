open Data_spec
open Core
open Ir

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
   `constraints` lists all the constraints (record predicates) on the elements
   stored in the containers from above.
   Each entry has a form of: <record predicate>, (<c-struct name>, <constraint list>)
   It is a pair of the name of the record predicate, and a pair consisting of the name
   of the c-struct that represents that record and a list of constraints that are in the form of
      Bop (<cmp>, {t=Unknown;v=<lhs>}, {t=Unknown;v=<rhs>})
   or Not {v=Bop (Eq, )}
   here <cmp> - is one of Le, Lt - for "less or equal", "less than"
        <lhs> and <rhs> are left- and right- hand side expressions that can be
        either Int <integer> or Id "<identifier>" which means an integer constant
            and a variable (or a field) name.
   === *)
let constraints = []

(* ===

   Leave these definition as is, they will be filled automatically

   === *)
let gen_custom_includes = ref []
let gen_records = ref []
