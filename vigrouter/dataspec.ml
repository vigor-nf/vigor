open Data_spec
open Core
open Ir

let containers = ["lpm", LPM ("route_condition");]
let custom_includes = []

let constraints = ["route_condition", ( "uint32_t",
                                         [Bop (Le, {t=Unknown;v=Int 0}, {t=Unknown;v=Id "route"});
                                          Bop (Lt, {t=Unknown;v=Id "route"}, {t=Unknown;v=Int 2});
                                         ])]

let gen_custom_includes : string list ref = ref []
let gen_records : (string * ttype) list ref = ref []
