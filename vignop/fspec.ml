open Core
open Str
open Fspec_api
open Ir
open Common_fspec

module Iface : Fspec_api.Spec =
struct
  let containers = []
  let records = String.Map.of_alist_exn []
end

let () = Fspec_api.spec := Some (module Iface) ;
