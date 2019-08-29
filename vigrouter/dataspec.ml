open Data_spec
open Core
open Ir

let containers = ["lpm", LPM ("route_condition");]
let custom_includes = []

(* TODO: add constraints *)
let constraints = []

let gen_custom_includes : string list ref = ref []
let gen_records : (string * ttype) list ref = ref []
