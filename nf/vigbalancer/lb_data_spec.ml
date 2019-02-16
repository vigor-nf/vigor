open Data_spec

let containers = ["flow_to_flow_id", Map ("LoadBalancedFlow", "flow_capacity", "lb_flow_id_condition");
                  "flow_heap", Vector ("LoadBalancedFlow", "flow_capacity", "");
                  "flow_chain", DChain "flow_capacity";
                  "flow_id_to_backend_id", Vector ("uint32_t", "flow_capacity", "lb_flow_id2backend_id_cond");
                  "backend_ips", Vector ("ip_addr", "backend_capacity", "");
                  "backends", Vector ("LoadBalancedBackend", "backend_capacity", "lb_backend_condition");
                  "ip_to_backend_id", Map ("ip_addr", "backend_capacity", "lb_backend_id_condition");
                  "active_backends", DChain "backend_capacity";
                  "cht", CHT ("backend_capacity", "cht_height");
                  "backend_capacity", UInt32;
                  "flow_capacity", UInt32;
                  "cht_height", UInt32;
                  "", EMap ("LoadBalancedFlow", "flow_to_flow_id", "flow_heap", "flow_chain");
                  "", EMap ("ip_addr", "ip_to_backend_id", "backend_ips", "active_backends");
                 ]

let loop_header_fname = "lb_loop.h"
let state_header_fname = "lb_state.h"
let loop_stub_fname = "lb_loop.c"
let state_fname = "lb_state.c"
let custom_includes = ["lb_flow.h.gen.h";
                       "lb_backend.h.gen.h";
                       "ip_addr.h.gen.h"]
