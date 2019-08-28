open Data_spec
open Core
open Ir

let containers = ["dyn_map", Map ("ip_addr", "capacity", "");
                  "dyn_keys", Vector ("ip_addr", "capacity", "");
                  "dyn_heap", DChain "capacity";
                  "dyn_vals", Vector ("DynamicValue", "capacity", "dyn_val_condition");
                  "capacity", UInt32;
                  "dev_count", UInt32;
                  "flow_emap", EMap ("ip_addr", "dyn_map", "dyn_keys", "dyn_heap");
                 ]

let constraints = ["dyn_val_condition", ( "DynamicValue",
                                          [Bop (Le, {t=Unknown;v=Int 0}, {t=Unknown;v=Id "bucket_time"});
                                           Bop (Le, {t=Unknown;v=Id "bucket_time"}, {t=Unknown;v=Id "t"});
                                           Bop (Le, {t=Unknown;v=Id "bucket_size"}, {t=Unknown;v=Int 3750000000});
                                          ])]

let gen_custom_includes = ref []
let gen_records = ref []

