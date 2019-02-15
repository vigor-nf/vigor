open Printf
open Data_spec

let containers = Nf_data_spec.containers


let inductive_name cname = match cname with
  | "uint32_t" -> "uint32_t"
  | _ -> cname ^ "i"

let predicate_name cname = match cname with
  | "uint32_t" -> "u_integer"
  | _ ->  cname ^ "p"

let constructor_name cname = match cname with
  | "uint32_t" -> "(uint32_t)"
  | _ ->  cname ^ "c"

let lhash_name cname = "_" ^ cname ^ "_hash"
let strdescrs_name cname = cname ^ "_descrs"
let nest_descrs_name cname = cname ^ "_nests"
let alloc_fun_name cname = cname ^ "_allocate"
let eq_fun_name cname = cname ^ "_eq"
let hash_fun_name cname = cname ^ "_hash"
let log_fun_name cname = "log_" ^ cname

let concat_flatten_map sep f lst extra =
  (String.concat sep ((List.flatten (List.map f lst))@extra))

let is_free_vector containers name =
  not (List.exists (fun (_,spec) ->
      match spec with
      | EMap (_, _, vec_name, _) -> String.equal name vec_name
      | _ -> false)
      containers)

let gen_loop_invariant containers =
  "/*@ predicate evproc_loop_invariant(" ^
  (concat_flatten_map ",\n                                    "
     (fun (name, cnt) ->
        match cnt with
        | Map (_, _) -> ["struct Map* " ^ name]
        | Vector (_, _) -> ["struct Vector* " ^ name]
        | CHT (_,_) -> ["struct Vector* " ^ name]
        | DChain _ -> ["struct DoubleChain* " ^ name]
        | UInt
        | UInt32
        | Int -> ["int " ^ name]
        | EMap (_, _, _, _) -> []
     )
     containers
     ["unsigned int lcore_id";
      "vigor_time_t time"]) ^
  ") = \n              " ^
  (concat_flatten_map " &*&\n              "
     (fun (name, cnt) ->
        match cnt with
        | Map (typ, cap) -> ["mapp<" ^ (inductive_name typ) ^ ">(" ^ name ^ ", " ^ (predicate_name typ) ^ ", " ^ (lhash_name typ) ^ ", " ^ "nop_true, " ^ "mapc(" ^ cap ^ ", ?_" ^ name ^ ", ?_" ^ name ^ "_addrs))"]
        | Vector (typ, cap) ->
          let vectorp = "vectorp<" ^ (inductive_name typ) ^ ">(" ^ name ^ ", " ^ (predicate_name typ) ^ ", ?_" ^ name ^ ", ?_" ^ name ^ "_addrs)"
          in
          let len = "length(_" ^ name ^ ") == " ^ cap in
          let is_one = "true == forall(_" ^ name ^ ", is_one)" in
          vectorp::
          (if is_free_vector containers name then [is_one] else [])@
          (if (String.equal cap "") || (String.equal cap "_") then [] else [len])
        | CHT (depth,height) ->
          let vectorp =
            "vectorp<uint32_t>(" ^ name ^ ", u_integer, ?_" ^ name ^ ", ?_" ^ name ^ "_addrs)"
          in
          let valid_cht = "true == valid_cht(_" ^ name ^ ", " ^ depth ^ ", " ^ height ^ ")"
          in
          [vectorp;valid_cht]
        | DChain cap -> ["double_chainp(?_" ^ name ^ ", " ^ name ^ ")";
                         "dchain_high_fp(_" ^ name ^ ") <= time";
                         "dchain_index_range_fp(_" ^ name ^ ") == " ^ cap]
        | UInt
        | UInt32
        | Int -> [name ^ " < INT_MAX"]
        | EMap (typ, m, v, ch) -> ["map_vec_chain_coherent<" ^ (inductive_name typ) ^ ">(_" ^ m ^ ", _" ^ v ^ ", _" ^ ch ^ ")";
                                   "true == forall2(_" ^ v ^ ", _" ^ v ^ "_addrs, (kkeeper)(_" ^ m ^ "_addrs))"]
     )
     containers
     ["lcore_id == 0";
      "last_time(time)"]
  ) ^ ";\n@*/"

let untraced_funs_args containers spaces =
  (concat_flatten_map (",\n" ^ spaces)
     (fun (name, cnt) ->
        match cnt with
        | Map (_, _) -> ["struct Map** " ^ name]
        | Vector (_, _) -> ["struct Vector** " ^ name]
        | CHT (_,_) -> ["struct Vector** " ^ name]
        | DChain _ -> ["struct DoubleChain** " ^ name]
        | Int -> ["int " ^ name]
        | UInt -> ["unsigned int " ^ name]
        | UInt32 -> ["uint32_t " ^ name]
        | EMap (_, _, _, _) -> []
     )
     containers
     ["unsigned int lcore_id";
      "vigor_time_t time"])


let gen_invariant_consume_decl containers =
  "void loop_invariant_consume(" ^
  (untraced_funs_args containers "                            ") ^
  ");\n" ^
  "/*@ requires " ^
  (concat_flatten_map " &*& "
     (fun (name, cnt) ->
        match cnt with
        | Map (_, _)
        | Vector (_, _)
        | CHT (_,_)
        | DChain _ -> ["*" ^ name ^ " |-> ?_" ^ name]
        | Int -> []
        | UInt -> []
        | UInt32 -> []
        | EMap (_, _, _, _) -> []
     ) containers []) ^ " &*&" ^
  "\n             evproc_loop_invariant(" ^
  (concat_flatten_map ", "

     (fun (name, cnt) ->
        match cnt with
        | Map (_, _)
        | Vector (_, _)
        | CHT (_, _)
        | DChain _ -> ["_" ^ name]
        | Int
        | UInt
        | UInt32 -> [name]
        | EMap (_, _, _, _) -> []
     ) containers ["lcore_id"; "time"]) ^ "); @*/\n" ^
  "/*@ ensures " ^
  (concat_flatten_map " &*& "
     (fun (name, cnt) ->
        match cnt with
        | Map (_, _)
        | Vector (_, _)
        | CHT (_, _)
        | DChain _ -> ["*" ^ name ^ " |-> _" ^ name]
        | Int -> []
        | UInt -> []
        | UInt32 -> []
        | EMap (_, _, _, _) -> []
     ) containers []) ^ "; @*/"

let gen_invariant_produce_decl containers =
  "void loop_invariant_produce(" ^
    (concat_flatten_map ",\n                            "
       (fun (name, cnt) ->
          match cnt with
          | Map (_, _) -> ["struct Map** " ^ name]
          | Vector (_, _) -> ["struct Vector** " ^ name]
          | CHT (_, _) -> ["struct Vector** " ^ name]
          | DChain _ -> ["struct DoubleChain** " ^ name]
          | Int -> ["int " ^ name]
          | UInt -> ["unsigned int " ^ name]
          | UInt32 -> ["uint32_t " ^ name]
          | EMap (_, _, _, _) -> []
       )
       containers
       ["unsigned int* lcore_id";
        "vigor_time_t* time"]) ^
  ");\n" ^
  "/*@ requires " ^
  (concat_flatten_map " &*& "
     (fun (name, cnt) ->
        match cnt with
        | Map (_, _)
        | Vector (_, _)
        | CHT (_, _)
        | DChain _ -> ["*" ^ name ^ " |-> ?_" ^ name]
        | Int -> []
        | UInt -> []
        | UInt32 -> []
        | EMap (_, _, _, _) -> []
     ) containers ["*lcore_id |-> _";
                   "*time |-> _"]) ^ ";@*/\n" ^
  "/*@ ensures " ^
  (concat_flatten_map " &*& "
     (fun (name, cnt) ->
        match cnt with
        | Map (_, _)
        | Vector (_, _)
        | CHT (_, _)
        | DChain _ -> ["*" ^ name ^ " |-> _" ^ name]
        | Int -> []
        | UInt -> []
        | UInt32 -> []
        | EMap (_, _, _, _) -> []
     ) containers ["*lcore_id |-> ?lcid";
                   "*time |-> ?t"]) ^ " &*&" ^
  "\n             evproc_loop_invariant(" ^
  (concat_flatten_map ", "
     (fun (name, cnt) ->
        match cnt with
        | Map (_, _)
        | Vector (_, _)
        | CHT (_, _)
        | DChain _ -> ["_" ^ name]
        | Int
        | UInt
        | UInt32 -> [name]
        | EMap (_, _, _, _) -> []
     ) containers ["lcid"; "t"]) ^ "); @*/\n"

let gen_loop_iteration_border_decl containers =
  "void loop_iteration_border(" ^
  (untraced_funs_args containers "                           ") ^
  ");\n"

let gen_loop_reset_impl containers =
  "void loop_reset(" ^
  (concat_flatten_map (",\n" ^ "                ")
     (fun (name, cnt) ->
        match cnt with
        | Map (_, _) -> ["struct Map** " ^ name]
        | Vector (_, _) -> ["struct Vector** " ^ name]
        | CHT (_, _) -> ["struct Vector** " ^ name]
        | DChain _ -> ["struct DoubleChain** " ^ name]
        | Int -> ["int " ^ name]
        | UInt -> ["unsigned int " ^ name]
        | UInt32 -> ["uint32_t " ^ name]
        | EMap (_, _, _, _) -> []
     )
     containers
     ["unsigned int lcore_id";
      "vigor_time_t* time"]) ^
  ")\n{\n" ^
  (concat_flatten_map ""
     (fun (name, cnt) ->
        match cnt with
        | Map (_, _) -> ["  map_reset(*" ^ name ^ ");\n"]
        | Vector (_, _) -> ["  vector_reset(*" ^ name ^ ");\n"]
        | CHT (_, _) -> ["  vector_reset(*" ^ name ^ ");\n"]
        | DChain cap -> ["  dchain_reset(*" ^ name ^ ", " ^ cap ^ ");\n"]
        | Int -> []
        | UInt -> []
        | UInt32 -> []
        | EMap (_, _, _, _) -> []
     )
     containers ["  *time = restart_time();\n"]) ^ "}"

let gen_loop_invariant_consume_stub containers =
  "void loop_invariant_consume(" ^
    (concat_flatten_map ",\n                            "
       (fun (name, cnt) ->
          match cnt with
          | Map (_, _) -> ["struct Map** " ^ name]
          | Vector (_, _) -> ["struct Vector** " ^ name]
          | CHT (_, _) -> ["struct Vector** " ^ name]
          | DChain _ -> ["struct DoubleChain** " ^ name]
          | Int -> ["int " ^ name]
          | UInt -> ["unsigned int " ^ name]
          | UInt32 -> ["uint32_t " ^ name]
          | EMap (_, _, _, _) -> []
       )
       containers
       ["unsigned int lcore_id";
        "vigor_time_t time"]) ^
  ")\n{\n" ^
  "  klee_trace_ret();\n" ^
    (concat_flatten_map ""
       (fun (name, cnt) ->
          match cnt with
          | Map (_, _) -> ["  klee_trace_param_ptr(" ^ name ^ ", sizeof(struct Map*), \"" ^ name ^ "\");\n"]
          | Vector (_, _) -> ["  klee_trace_param_ptr(" ^ name ^ ", sizeof(struct Vector*), \"" ^ name ^ "\");\n"]
          | CHT (_, _) -> ["  klee_trace_param_ptr(" ^ name ^ ", sizeof(struct Vector*), \"" ^ name ^ "\");\n"]
          | DChain _ -> ["  klee_trace_param_ptr(" ^ name ^ ", sizeof(struct DoubleChain*), \"" ^ name ^ "\");\n"]
          | Int -> ["  klee_trace_param_i32(" ^ name ^ ", \"" ^ name ^ "\");\n"]
          | UInt -> ["  klee_trace_param_u32(" ^ name ^ ", \"" ^ name ^ "\");\n"]
          | UInt32 -> ["  klee_trace_param_u32(" ^ name ^ ", \"" ^ name ^ "\");\n"]
          | EMap (_, _, _, _) -> []
       )
       containers
       ["  klee_trace_param_i32(lcore_id, \"lcore_id\");\n";
        "  klee_trace_param_i64(time, \"time\");\n"]) ^ "}"

let gen_loop_invariant_produce_stub containers =
  "void loop_invariant_produce(" ^
    (concat_flatten_map ",\n                            "
       (fun (name, cnt) ->
          match cnt with
          | Map (_, _) -> ["struct Map** " ^ name]
          | Vector (_, _) -> ["struct Vector** " ^ name]
          | CHT (_, _) -> ["struct Vector** " ^ name]
          | DChain _ -> ["struct DoubleChain** " ^ name]
          | Int -> ["int " ^ name]
          | UInt -> ["unsigned int " ^ name]
          | UInt32 -> ["uint32_t " ^ name]
          | EMap (_, _, _, _) -> []
       )
       containers
       ["unsigned int* lcore_id";
        "vigor_time_t* time"]) ^
  ")\n{\n" ^
  "  klee_trace_ret();\n" ^
    (concat_flatten_map ""
       (fun (name, cnt) ->
          match cnt with
          | Map (_, _) -> ["  klee_trace_param_ptr(" ^ name ^ ", sizeof(struct Map*), \"" ^ name ^ "\");\n"]
          | Vector (_, _) -> ["  klee_trace_param_ptr(" ^ name ^ ", sizeof(struct Vector*), \"" ^ name ^ "\");\n"]
          | CHT (_, _) -> ["  klee_trace_param_ptr(" ^ name ^ ", sizeof(struct Vector*), \"" ^ name ^ "\");\n"]
          | DChain _ -> ["  klee_trace_param_ptr(" ^ name ^ ", sizeof(struct DoubleChain*), \"" ^ name ^ "\");\n"]
          | Int -> ["  klee_trace_param_i32(" ^ name ^ ", \"" ^ name ^ "\");\n"]
          | UInt -> ["  klee_trace_param_u32(" ^ name ^ ", \"" ^ name ^ "\");\n"]
          | UInt32 -> ["  klee_trace_param_u32(" ^ name ^ ", \"" ^ name ^ "\");\n"]
          | EMap (_, _, _, _) -> []
       )
       containers
       ["  klee_trace_param_ptr(lcore_id, sizeof(unsigned int), \"lcore_id\");\n";
        "  klee_trace_param_ptr(time, sizeof(vigor_time_t), \"time\");\n"]) ^ "}"

let gen_loop_iteration_border_stub containers =
  "void loop_iteration_border(" ^
  (untraced_funs_args containers "                           ") ^
  ")\n{\n" ^
  "  loop_invariant_consume(" ^
  (concat_flatten_map ", "
     (fun (name, cnt) ->
        match cnt with
        | EMap (_, _, _, _) -> []
        | _ -> [name])
     containers ["lcore_id"; "time"]) ^ ");\n" ^
  "  loop_reset(" ^
  (concat_flatten_map ", "
     (fun (name, cnt) ->
        match cnt with
        | EMap (_, _, _, _) -> []
        | _ -> [name])
     containers ["lcore_id"; "&time"]) ^ ");\n" ^
  "  loop_invariant_produce(" ^
  (concat_flatten_map ", "
     (fun (name, cnt) ->
        match cnt with
        | EMap (_, _, _, _) -> []
        | _ -> [name])
     containers
     ["&lcore_id"; "&time"]) ^ ");\n" ^
  "}"

let () =
  let cout = open_out Nf_data_spec.header_fname in
  fprintf cout "#ifndef _LOOP_H_INCLUDED_\n";
  fprintf cout "#define _LOOP_H_INCLUDED_\n";
  fprintf cout "#include \"lib/containers/double-chain.h\"\n";
  fprintf cout "#include \"lib/containers/map.h\"\n";
  fprintf cout "#include \"lib/containers/vector.h\"\n";
  fprintf cout "#include \"lib/containers/cht.h\"\n";
  fprintf cout "#include \"lib/coherence.h\"\n";
  fprintf cout "#include \"lib/nf_time.h\"\n";
  List.iter (fun incl ->
      fprintf cout "#include \"%s\"\n" incl;)
    Nf_data_spec.custom_includes;
  fprintf cout "%s\n" (gen_loop_invariant containers);
  fprintf cout "%s\n" (gen_invariant_consume_decl containers);
  fprintf cout "%s\n" (gen_invariant_produce_decl containers);
  fprintf cout "%s\n" (gen_loop_iteration_border_decl containers);
  fprintf cout "#endif//_LOOP_H_INCLUDED_\n";
  close_out cout;
  let cout = open_out Nf_data_spec.stub_fname in
  fprintf cout "#include <klee/klee.h>\n";
  fprintf cout "#include \"%s\"\n" Nf_data_spec.header_fname;
  fprintf cout "#include \"lib/stubs/time_stub_control.h\"\n";
  fprintf cout "#include \"lib/stubs/containers/double-chain-stub-control.h\"\n";
  fprintf cout "#include \"lib/stubs/containers/map-stub-control.h\"\n";
  fprintf cout "#include \"lib/stubs/containers/vector-stub-control.h\"\n";
  fprintf cout "%s\n" (gen_loop_reset_impl containers);
  fprintf cout "%s\n" (gen_loop_invariant_consume_stub containers);
  fprintf cout "%s\n" (gen_loop_invariant_produce_stub containers);
  fprintf cout "%s\n" (gen_loop_iteration_border_stub containers);
  close_out cout;
