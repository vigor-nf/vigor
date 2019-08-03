open Core
open Str
open Fspec_api
open Ir
open Common_fspec

(* ===
  This file describes the state of the NF.
  Due to the prototype nature of Vigor, YOU MUST MIRROR CHANGES TO STRUCTURE HEADERS HERE (see example file 'flow.h')
  AND ALSO MIRROR CHANGES HERE TO THE DATASPEC FILES (see example files 'dataspec.ml'/'dataspec.py')
  SOSPTODO Arseniy please describe how to write this file...
   === *)

let flow_id_struct = Ir.Str ( "FlowId", ["src_port", Uint16;
                                         "dst_port", Uint16;
                                         "src_ip", Uint32;
                                         "dst_ip", Uint32;
                                         "protocol", Uint8;] )

module Iface : Fspec_api.Spec =
struct
  let containers = ["example_value", UInt32;]

  let records = String.Map.of_alist_exn
                ["FlowId", flow_id_struct]
end

(* Register the module *)
let () = Fspec_api.spec := Some (module Iface) ;
