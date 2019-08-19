open Core
open Str
open Fspec_api
open Ir
open Common_fspec

(* ===
  This file describes the state of the NF.
  Due to the prototype nature of Vigor,
  YOU MUST MIRROR CHANGES TO STRUCTURE HEADERS HERE (see example file 'flow.h')
  AND ALSO MIRROR CHANGES HERE TO THE DATASPEC FILES
  (see example files 'dataspec.ml'/'dataspec.py')

  Two need to define two lists in the Iface module: containers and records.
  You are free to use auxiliary definitions, like flow_id_struct below.
   === *)

(* ===
   This is a helper definition of a C struct flow_id with 5 fields.
   UintNN corresponds to ctype uintNN_t
   SintNN corresponds to ctype intNN_t
   In C this structure definition looks like this:
   struct flow_id {
     uint16_t src_port;
     uint16_t dst_port;
     uint32_t src_ip;
     uint32_t dst_ip;
     uint8_t protocol;
   };
   === *)
let flow_id_struct = Ir.Str ( "FlowId", ["src_port", Uint16;
                                         "dst_port", Uint16;
                                         "src_ip", Uint32;
                                         "dst_ip", Uint32;
                                         "protocol", Uint8;] )

module Iface : Fspec_api.Spec =
struct
  (* ===
     `containers` list is taken directly from the dataspec.ml file.
     Briefly, it is a declaration of all the state NF persists between
     packet processing iterations.
     See dataspec.ml for more details.
     === *)
  let containers = ["example_value", UInt32;]

  (* ===
     `records` list declares all the record types used in the NF.
     It consists of pairs separated by semicolon.
     Each pair consists of a string -
     name of the record type used in the `containers` list,
     followed by a comma and by an OCaml definition of that record.
     The OCaml definition may be
     - A simple type (e.g. Uint32)
     - Ir.Str (....) - a C struct (e.g. flow_id_struct)
     === *)
  let records = String.Map.of_alist_exn
                ["FlowId", flow_id_struct]
end

(* Register the module *)
let () = Fspec_api.spec := Some (module Iface) ;
