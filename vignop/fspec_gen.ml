open Data_spec
open Core
open Ir

let containers = []
let custom_includes = []

let constraints = []
let gen_custom_includes : string list ref = ref []
let gen_records : (string * ttype) list ref = ref []
