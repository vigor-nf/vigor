open Core
open Str
open Fspec_api
open Ir
open Common_fspec

let flow_id_struct = Ir.Str ( "FlowId", ["src_port", Uint16;
                                         "dst_port", Uint16;
                                         "src_ip", Uint32;
                                         "dst_ip", Uint32;
                                         "protocol", Uint8;] )

module Iface : Fspec_api.Spec =
struct
(* FIXME: borrowed from ../nf/vigfw/fw_data_spec.ml *)
let containers = ["fm", Map ("FlowId", "max_flows", "");
                  "fv", Vector ("FlowId", "max_flows", "");
                  "int_devices", Vector ("uint32_t", "max_flows", "int_dev_bounds");
                  "heap", DChain "max_flows";
                  "max_flows", Int;
                  "fw_device", UInt32;
                  "flow_emap", EMap ("FlowId", "fm", "fv", "heap")]

let records = String.Map.of_alist_exn
    ["FlowId", flow_id_struct;
     "uint32_t", Uint32;]
end

(* Register the module *)
let () =
  Fspec_api.spec := Some (module Iface) ;

