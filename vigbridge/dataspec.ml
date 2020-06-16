open Data_spec
open Core
open Ir

let containers = ["dyn_map", Map ("rte_ether_addr", "capacity", "");
                  "dyn_keys", Vector ("rte_ether_addr", "capacity", "");
                  "dyn_vals", Vector ("DynamicValue", "capacity", "dyn_val_condition");
                  "st_map", Map ("StaticKey", "stat_capacity", "stat_map_condition");
                  "st_vec", Vector ("StaticKey", "stat_capacity", "");
                  "dyn_heap", DChain "capacity";
                  "capacity", UInt32;
                  "stat_capacity", UInt32;
                  "dev_count", UInt32;
                  "dyn_emap", EMap ("rte_ether_addr", "dyn_map", "dyn_keys", "dyn_heap")]

let constraints = ["dyn_val_condition", ( "DynamicValue",
                                          [Bop (Le, {t=Unknown;v=Int 0}, {t=Unknown;v=Id "device"});
                                           Bop (Lt, {t=Unknown;v=Id "device"}, {t=Unknown;v=Int 2});
                                          ]);
                   "stat_map_condition", ( "StaticKey",
                                           [Bop (Le, {t=Unknown;v=Int 0}, {t=Unknown;v=Id "index"});
                                            Bop (Lt, {t=Unknown;v=Id "index"}, {t=Unknown;v=Int 2});
                                           ])]

let gen_custom_includes = ref []
let gen_records = ref []
