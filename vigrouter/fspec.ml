open Core
open Str
open Fspec_api
open Ir
open Common_fspec

module Iface : Fspec_api.Spec =
struct
  let containers = ["lpm", LPM ("route_condition");]

  let records = String.Map.of_alist_exn
                []
end

(* Register the module *)
let () = Fspec_api.spec := Some (module Iface) ;
