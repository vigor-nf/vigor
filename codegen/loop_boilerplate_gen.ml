open Printf
open Ir
open Data_spec

let gen_records = !Nf_data_spec.gen_records
let containers = Nf_data_spec.containers
let constraints = Nf_data_spec.constraints


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
let alloc_fun_name cname = match cname with
  | "uint32_t" -> "null_init"
  | _ ->  cname ^ "_allocate"

let eq_fun_name cname = cname ^ "_eq"
let hash_fun_name cname = cname ^ "_hash"
let log_fun_name cname = "log_" ^ cname
let advance_time_lemma inv = "advance_time_" ^ inv
let init_lemma inv = "init_" ^ inv
let logic_name inv = inv ^ "l"
let default_value_for typ = "DEFAULT_" ^ (String.uppercase_ascii typ)
let constructor_name cstruct_name = cstruct_name ^ "c"

let concat_flatten_map sep f lst extra =
  (String.concat sep ((List.flatten (List.map f lst))@extra))

let is_free_vector containers name =
  not (List.exists (fun (_,spec) ->
      match spec with
      | EMap (_, _, vec_name, _) -> String.equal name vec_name
      | _ -> false)
      containers)

let destruct_record name =
  (constructor_name name) ^ "(" ^
  (match List.assoc_opt name gen_records with
     | Some (Ir.Str (strname, fields)) ->
       (concat_flatten_map ", " (fun (name,_) ->
            [name]) fields [])
     | _ -> "unsupported struct") ^ ")"

let condition_kind containers condition =
  let container = (List.find_opt (function
      | _, Vector (_, _, invariant) when invariant = condition -> true
      | _, Map (_, _, invariant) when invariant = condition -> true
      | _, LPM (invariant) when invariant = condition -> true
      | _ -> false))
    containers
  in
  match container with
  | Some (_, Vector (_, _, _)) -> `Vector
  | Some (_, Map (_, _, _)) -> `Map
  | Some (_, LPM (_)) -> `LPM
  | _ -> `Unknown

let gen_inv_conditions constraints containers =
  "/*@\n" ^
  (concat_flatten_map "\n"
     (fun (inv_name, (cstruct, exps)) ->
        match condition_kind containers inv_name with
        | `Vector ->
          ["fixpoint bool " ^ logic_name inv_name ^
           "(vigor_time_t t, " ^ inductive_name cstruct ^
           " v) {\n" ^
           (if cstruct = "uint32_t" then
              "return " ^ (concat_flatten_map " && "
                             (fun term -> [render_term term]) exps []) ^
              ";\n"
            else
           "switch(v) {\n\
            case " ^ destruct_record cstruct ^
           ":\n\
            return " ^ (concat_flatten_map " && "
                          (fun term -> [render_term term]) exps []) ^
           ";\n\
            }\n") ^
           "}\n\
           "]
        | `Map ->
          ["fixpoint bool " ^ logic_name inv_name ^
           "(vigor_time_t t, pair<" ^ inductive_name cstruct ^
           ", int> p) {\n\
            switch(p) { case pair(value, index):\n\
            return switch(value) {\n\
            case " ^ destruct_record cstruct ^
           ":\n\
            return " ^ (concat_flatten_map " && "
                          (fun term -> [render_term term]) exps []) ^
           ";\n\
            };\n\
            }\n\
            }\n\
           "]
        | `LPM ->
          ["fixpoint bool " ^ logic_name inv_name ^
           "(pair<" ^ inductive_name cstruct ^
           ", int> p) {\n\
            switch(p) { case pair(value, index):\n\
            return switch(value) {\n\
            case " ^ destruct_record cstruct ^
           ":\n\
            return " ^ (concat_flatten_map " && "
                          (fun term -> [render_term term]) exps []) ^
           ";\n\
            };\n\
            }\n\
            }\n\
           "]
        | `Unknown ->
          ["Unknown condition kind: " ^ inv_name]
     ) constraints []) ^
  "@*/"

let gen_inv_lemmas containers =
  "/*@\n" ^
  (concat_flatten_map "\n"
     (fun (name, cnt) ->
        match cnt with
        | Vector (typ, _, invariant) when invariant <> "" -> [
            "lemma void " ^ (advance_time_lemma invariant) ^ "(list<pair<" ^
            inductive_name typ ^
            ", real> > vec,\n\
             vigor_time_t old_time,\n\
             vigor_time_t new_time)\n\
             requires true == forall(vec, (sup)((" ^
            (logic_name invariant) ^
            ")(old_time), fst)) &*&\n\
            old_time <= new_time;\n\
             ensures true == forall(vec, (sup)((" ^
            (logic_name invariant) ^
            ")(new_time), fst));\n\
            {\n\
             switch(vec) {\n\
            case nil:\n\
            case cons(h,t):\n\
            " ^ (advance_time_lemma invariant) ^
            "(t, old_time, new_time);\n\
             switch(h) {case pair(v, fr):\n" ^
            (if typ <> "uint32_t" then
               "switch(v) { case " ^ (destruct_record typ) ^":}\n"
             else ""
            ) ^
            "}\n\
             }\n\
             }\n";
            "lemma void " ^ (init_lemma invariant) ^
            "(nat cap, vigor_time_t time)\n\
             requires 0 <= time;\n\
             ensures true == forall(repeat(pair(" ^ (default_value_for typ) ^
            ", 1.0), cap), (sup)((" ^
            (logic_name invariant) ^
            ")(time), fst));\n\
             {\n\
             switch(cap) {\n\
             case zero:\n\
             case succ(n):\n\
            " ^ (init_lemma invariant) ^
            "(n, time);\n\
             }\n\
             }\n"
          ]
        | Map (typ, _, invariant) when invariant <> "" -> [
            "lemma void " ^ (advance_time_lemma invariant) ^ "(list<pair<" ^
            inductive_name typ ^
            ", int> > map,\n\
             vigor_time_t old_time,\n\
             vigor_time_t new_time)\n\
             requires true == forall(map, (" ^
            (logic_name invariant) ^
            ")(old_time)) &*&\n\
            old_time <= new_time;\n\
             ensures true == forall(map, (" ^
            (logic_name invariant) ^
            ")(new_time));\n\
            {\n\
             switch(map) {\n\
            case nil:\n\
            case cons(h,t):\n\
            " ^ (advance_time_lemma invariant) ^
            "(t, old_time, new_time);\n\
             switch(h) {case pair(v, fr):\n\
             switch(v) { case " ^ (destruct_record typ) ^":}
             }\n\
             }\n\
             }\n";
          ]
        | Vector (_, _, _)
        | Map (_, _, _)
        | CHT (_,_)
        | DChain _
        | UInt
        | UInt32
        | Int
        | EMap (_, _, _, _)
        | LPM _ -> []
     )
     containers
     []) ^
  "@*/"

let gen_loop_invariant containers =
  "/*@ predicate evproc_loop_invariant(" ^
  (concat_flatten_map ",\n                                    "
     (fun (name, cnt) ->
        match cnt with
        | Map (_, _, _) -> ["struct Map* " ^ name]
        | Vector (_, _, _) -> ["struct Vector* " ^ name]
        | CHT (_,_) -> ["struct Vector* " ^ name]
        | DChain _ -> ["struct DoubleChain* " ^ name]
        | UInt
        | UInt32
        | Int -> ["int " ^ name]
        | EMap (_, _, _, _) -> []
        | LPM _ -> ["struct lpm* " ^ name]
     )
     containers
     ["unsigned int lcore_id";
      "vigor_time_t time"]) ^
  ") = \n              " ^
  (concat_flatten_map " &*&\n              "
     (fun (name, cnt) ->
        match cnt with
        | Map (typ, cap, invariant) ->
          ["mapp<" ^ (inductive_name typ) ^ ">(" ^
           name ^ ", " ^ (predicate_name typ) ^
           ", " ^ (lhash_name typ) ^ ", " ^ "nop_true, " ^
           "mapc(" ^ cap ^ ", ?_" ^ name ^ ", ?_" ^ name ^
           "_addrs))"]@
          (if invariant = "" then [] else
             ["true == forall(_" ^ name ^ ", (" ^
              (logic_name invariant) ^ ")(time))"])
        | Vector (typ, cap, invariant) ->
          let vectorp = "vectorp<" ^ (inductive_name typ) ^
                        ">(" ^ name ^ ", " ^ (predicate_name typ) ^
                        ", ?_" ^ name ^ ", ?_" ^ name ^ "_addrs)"
          in
          let len = "length(_" ^ name ^ ") == " ^ cap in
          let is_one = "true == forall(_" ^ name ^ ", is_one)" in
          let cell_inv =
            "true == forall(_" ^ name ^ ", (sup)((" ^ (logic_name invariant) ^ ")(time), fst))"
          in
          vectorp::
          (if is_free_vector containers name then [is_one] else [])@
          (if invariant <> "" then [cell_inv] else [])@
          (if (String.equal cap "") || (String.equal cap "_") then [] else [len])
        | CHT (depth,height) ->
          let vectorp =
            "vectorp<uint32_t>(" ^ name ^ ", u_integer, ?_" ^ name ^
            ", ?_" ^ name ^ "_addrs)"
          in
          let valid_cht = "true == valid_cht(_" ^ name ^ ", " ^ depth ^
                          ", " ^ height ^ ")"
          in
          [vectorp;valid_cht]
        | DChain cap -> ["double_chainp(?_" ^ name ^ ", " ^ name ^ ")";
                         "dchain_high_fp(_" ^ name ^ ") <= time";
                         "dchain_index_range_fp(_" ^ name ^ ") == " ^ cap]
        | UInt
        | UInt32
        | Int -> [name ^ " < INT_MAX"]
        | EMap (typ, m, v, ch) -> ["map_vec_chain_coherent<" ^ (inductive_name typ) ^
                                   ">(_" ^ m ^ ", _" ^ v ^ ", _" ^ ch ^ ")";
                                   "true == forall2(_" ^ v ^ ", _" ^ v ^
                                   "_addrs, (kkeeper)(_" ^ m ^ "_addrs))"]
        | LPM _ -> ["table(" ^ name ^ ", ?_" ^ name ^ ")";]
     )
     containers
     ["lcore_id == 0";
      "last_time(time)"]
  ) ^ ";\n@*/"

let untraced_funs_args containers spaces =
  (concat_flatten_map (",\n" ^ spaces)
     (fun (name, cnt) ->
        match cnt with
        | Map (_, _, _) -> ["struct Map** " ^ name]
        | Vector (_, _, _) -> ["struct Vector** " ^ name]
        | CHT (_,_) -> ["struct Vector** " ^ name]
        | DChain _ -> ["struct DoubleChain** " ^ name]
        | Int -> ["int " ^ name]
        | UInt -> ["unsigned int " ^ name]
        | UInt32 -> ["uint32_t " ^ name]
        | EMap (_, _, _, _) -> []
        | LPM _ -> ["struct lpm** " ^ name]
     )
     containers
     ["unsigned int lcore_id";
      "vigor_time_t time"])


let gen_invariant_consume_decl containers =
  "void loop_invariant_consume(" ^
  (untraced_funs_args containers "                            ") ^
  ");\n" ^
  "/*@ requires " ^
  (concat_flatten_map ""
     (fun (name, cnt) ->
        match cnt with
        | Map (_, _, _)
        | Vector (_, _, _)
        | CHT (_,_)
        | LPM _
        | DChain _ -> ["*" ^ name ^ " |-> ?_" ^ name ^ " &*& "]
        | Int -> []
        | UInt -> []
        | UInt32 -> []
        | EMap (_, _, _, _) -> []
     ) containers []) ^
  "\n             evproc_loop_invariant(" ^
  (concat_flatten_map ", "

     (fun (name, cnt) ->
        match cnt with
        | Map (_, _, _)
        | Vector (_, _, _)
        | CHT (_, _)
        | LPM _
        | DChain _ -> ["_" ^ name]
        | Int
        | UInt
        | UInt32 -> [name]
        | EMap (_, _, _, _) -> []
     ) containers ["lcore_id"; "time"]) ^ "); @*/\n" ^
  "/*@ ensures " ^
  (concat_flatten_map ""
     (fun (name, cnt) ->
        match cnt with
        | Map (_, _, _)
        | Vector (_, _, _)
        | CHT (_, _)
        | LPM _
        | DChain _ -> ["*" ^ name ^ " |-> _" ^ name ^ " &*& "]
        | Int -> []
        | UInt -> []
        | UInt32 -> []
        | EMap (_, _, _, _) -> []
     ) containers []) ^ "true; @*/"

let gen_invariant_produce_decl containers =
  "void loop_invariant_produce(" ^
    (concat_flatten_map ",\n                            "
       (fun (name, cnt) ->
          match cnt with
          | Map (_, _, _) -> ["struct Map** " ^ name]
          | Vector (_, _, _) -> ["struct Vector** " ^ name]
          | CHT (_, _) -> ["struct Vector** " ^ name]
          | DChain _ -> ["struct DoubleChain** " ^ name]
          | Int -> ["int " ^ name]
          | UInt -> ["unsigned int " ^ name]
          | UInt32 -> ["uint32_t " ^ name]
          | EMap (_, _, _, _) -> []
          | LPM _ -> ["struct lpm** " ^ name]
       )
       containers
       ["unsigned int* lcore_id";
        "vigor_time_t* time"]) ^
  ");\n" ^
  "/*@ requires " ^
  (concat_flatten_map " &*& "
     (fun (name, cnt) ->
        match cnt with
        | Map (_, _, _)
        | Vector (_, _, _)
        | CHT (_, _)
        | LPM _
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
        | Map (_, _, _)
        | Vector (_, _, _)
        | CHT (_, _)
        | LPM _
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
        | Map (_, _, _)
        | Vector (_, _, _)
        | CHT (_, _)
        | LPM _
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
        | Map (_, _, _) -> ["struct Map** " ^ name]
        | Vector (_, _, _) -> ["struct Vector** " ^ name]
        | CHT (_, _) -> ["struct Vector** " ^ name]
        | DChain _ -> ["struct DoubleChain** " ^ name]
        | Int -> ["int " ^ name]
        | UInt -> ["unsigned int " ^ name]
        | UInt32 -> ["uint32_t " ^ name]
        | EMap (_, _, _, _) -> []
        | LPM _ -> ["struct lpm** " ^ name]
     )
     containers
     ["unsigned int lcore_id";
      "vigor_time_t* time"]) ^
  ")\n{\n" ^
  (concat_flatten_map ""
     (fun (name, cnt) ->
        match cnt with
        | Map (_, _, _) -> ["  map_reset(*" ^ name ^ ");\n"]
        | Vector (_, _, _) -> ["  vector_reset(*" ^ name ^ ");\n"]
        | CHT (_, _) -> ["  vector_reset(*" ^ name ^ ");\n"]
        | DChain cap -> ["  dchain_reset(*" ^ name ^ ", " ^ cap ^ ");\n"]
        | Int -> []
        | UInt -> []
        | UInt32 -> []
        | EMap (_, _, _, _) -> []
        | LPM _ -> []
     )
     containers ["  *time = restart_time();\n"]) ^ "}"

let gen_loop_invariant_consume_stub containers =
  "void loop_invariant_consume(" ^
    (concat_flatten_map ",\n                            "
       (fun (name, cnt) ->
          match cnt with
          | Map (_, _, _) -> ["struct Map** " ^ name]
          | Vector (_, _, _) -> ["struct Vector** " ^ name]
          | CHT (_, _) -> ["struct Vector** " ^ name]
          | DChain _ -> ["struct DoubleChain** " ^ name]
          | Int -> ["int " ^ name]
          | UInt -> ["unsigned int " ^ name]
          | UInt32 -> ["uint32_t " ^ name]
          | EMap (_, _, _, _) -> []
          | LPM _ -> ["struct lpm** " ^ name]
       )
       containers
       ["unsigned int lcore_id";
        "vigor_time_t time"]) ^
  ")\n{\n" ^
  "  klee_trace_ret();\n" ^
    (concat_flatten_map ""
       (fun (name, cnt) ->
          match cnt with
          | Map (_, _, _) -> ["  klee_trace_param_ptr(" ^
                              name ^ ", sizeof(struct Map*), \"" ^
                              name ^ "\");\n"]
          | Vector (_, _, _) -> ["  klee_trace_param_ptr(" ^
                                 name ^ ", sizeof(struct Vector*), \"" ^
                                 name ^ "\");\n"]
          | CHT (_, _) -> ["  klee_trace_param_ptr(" ^
                           name ^ ", sizeof(struct Vector*), \"" ^
                           name ^ "\");\n"]
          | DChain _ -> ["  klee_trace_param_ptr(" ^
                         name ^ ", sizeof(struct DoubleChain*), \"" ^
                         name ^ "\");\n"]
          | Int -> ["  klee_trace_param_i32(" ^
                    name ^ ", \"" ^
                    name ^ "\");\n"]
          | UInt -> ["  klee_trace_param_u32(" ^
                     name ^ ", \"" ^
                     name ^ "\");\n"]
          | UInt32 -> ["  klee_trace_param_u32(" ^
                       name ^ ", \"" ^
                       name ^ "\");\n"]
          | EMap (_, _, _, _) -> []
          | LPM _ -> ["  klee_trace_param_ptr(" ^
                      name ^ ", sizeof(struct lpm*), \"" ^
                      name ^ "\");\n"]
       )
       containers
       ["  klee_trace_param_i32(lcore_id, \"lcore_id\");\n";
        "  klee_trace_param_i64(time, \"time\");\n"]) ^ "}"

let gen_loop_invariant_produce_stub containers =
  "void loop_invariant_produce(" ^
    (concat_flatten_map ",\n                            "
       (fun (name, cnt) ->
          match cnt with
          | Map (_, _, _) -> ["struct Map** " ^ name]
          | Vector (_, _, _) -> ["struct Vector** " ^ name]
          | CHT (_, _) -> ["struct Vector** " ^ name]
          | DChain _ -> ["struct DoubleChain** " ^ name]
          | Int -> ["int " ^ name]
          | UInt -> ["unsigned int " ^ name]
          | UInt32 -> ["uint32_t " ^ name]
          | EMap (_, _, _, _) -> []
          | LPM _ -> ["struct lpm** " ^ name]
       )
       containers
       ["unsigned int* lcore_id";
        "vigor_time_t* time"]) ^
  ")\n{\n" ^
  "  klee_trace_ret();\n" ^
    (concat_flatten_map ""
       (fun (name, cnt) ->
          match cnt with
          | Map (_, _, _) -> ["  klee_trace_param_ptr(" ^
                              name ^ ", sizeof(struct Map*), \"" ^
                              name ^ "\");\n"]
          | Vector (_, _, _) -> ["  klee_trace_param_ptr(" ^
                                 name ^ ", sizeof(struct Vector*), \"" ^
                                 name ^ "\");\n"]
          | CHT (_, _) -> ["  klee_trace_param_ptr(" ^
                           name ^ ", sizeof(struct Vector*), \"" ^
                           name ^ "\");\n"]
          | DChain _ -> ["  klee_trace_param_ptr(" ^
                         name ^ ", sizeof(struct DoubleChain*), \"" ^
                         name ^ "\");\n"]
          | Int -> ["  klee_trace_param_i32(" ^
                    name ^ ", \"" ^
                    name ^ "\");\n"]
          | UInt -> ["  klee_trace_param_u32(" ^
                     name ^ ", \"" ^
                     name ^ "\");\n"]
          | UInt32 -> ["  klee_trace_param_u32(" ^
                       name ^ ", \"" ^
                       name ^ "\");\n"]
          | EMap (_, _, _, _) -> []
          | LPM _ -> ["  klee_trace_param_ptr(" ^
                      name ^ ", sizeof(struct lpm*), \"" ^
                      name ^ "\");\n"]
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

let gen_struct containers =
  "struct State {\n" ^
  (concat_flatten_map ""
     (fun (name, cnt) ->
        match cnt with
        | Map (_, _, _) -> ["  struct Map* " ^ name ^ ";\n"]
        | Vector (_, _, _)
        | CHT (_, _) -> ["  struct Vector* " ^ name ^ ";\n"]
        | DChain _ -> ["  struct DoubleChain* " ^ name ^ ";\n"]
        | Int -> ["  int " ^ name ^ ";\n"]
        | UInt -> ["  unsigned int " ^ name ^ ";\n"]
        | UInt32 -> ["  uint32_t " ^ name ^ ";\n"]
        | EMap (_, _, _, _) -> []
        | LPM _ -> ["  struct lpm* " ^ name ^ ";\n"]
     )
     containers []) ^
  "};\n"

let gen_allocation_proto containers =
  "struct State* alloc_state(" ^
  (concat_flatten_map ", "
     (fun (name, cnt) ->
        match cnt with
        | Map (_, _, _) -> []
        | Vector (_, _, _)
        | CHT (_, _) -> []
        | DChain _ -> []
        | Int -> ["int " ^ name]
        | UInt -> ["unsigned int " ^ name]
        | UInt32 -> ["uint32_t " ^ name]
        | EMap (_, _, _, _) -> []
        | LPM _ -> []
     )
     containers []) ^
  ")"

let gen_allocation containers =
  let abort_on_null allocation =
    "  if (" ^ allocation ^ " == 0) return NULL;\n"
  in
  (gen_allocation_proto containers) ^ "\n{\n" ^
  "  if (allocated_nf_state != NULL) return allocated_nf_state;\n" ^
  "  struct State* ret = malloc(sizeof(struct State));\n" ^
  "  if (ret == NULL) return NULL;\n" ^
  (concat_flatten_map ""
     (fun (name, cnt) ->
        match cnt with
        | Map (typ, cap, _) ->
          ["  ret->" ^ name ^ " = NULL;\n";
           abort_on_null ("map_allocate(" ^ eq_fun_name typ ^
                          ", " ^ hash_fun_name typ ^ ", " ^ cap ^
                          ", &(ret->" ^ name ^ "))")]
        | Vector (typ, cap, _) ->
          let typ_size =
            if String.equal typ "uint32_t" then
              "sizeof(uint32_t)" else
              "sizeof(struct " ^ typ ^ ")"
          in
          ["  ret->" ^ name ^ " = NULL;\n";
           abort_on_null ("vector_allocate(" ^ typ_size ^ ", " ^ cap ^
                          ", " ^ alloc_fun_name typ ^ ", &(ret->" ^ name ^ "))")]
        | CHT (depth, height) ->
          ["  ret->" ^ name ^ " = NULL;\n";
           abort_on_null ("vector_allocate(sizeof(uint32_t), " ^
                          depth ^ "*" ^ height ^ ", null_init, &(ret->" ^
                          name ^ "))");
           "  " ^ abort_on_null ("cht_fill_cht(ret->" ^
                                 name ^ ", " ^ height ^
                                 ", " ^ depth ^ ")")]
        | DChain cap -> ["  ret->" ^ name ^ " = NULL;\n";
                         abort_on_null ("dchain_allocate(" ^
                                        cap ^ ", &(ret->" ^ name ^ "))")]
        | Int
        | UInt
        | UInt32 -> ["  ret->" ^ name ^ " = " ^ name ^ ";\n"]
        | EMap (_, _, _, _) -> []
        | LPM _ -> ["  ret->" ^ name ^ " = NULL;\n";
                    abort_on_null ("lpm_allocate(&(ret->" ^ name ^ "))")]
     )
     containers []) ^
  "#ifdef KLEE_VERIFICATION\n" ^
  (concat_flatten_map ""
     (fun (name, cnt) ->
        match cnt with
        | Map (typ, cap, cond) ->
          ("  map_set_layout(ret->" ^ name ^ ", " ^ strdescrs_name typ ^
           ", sizeof(" ^ strdescrs_name typ ^
           ")/sizeof(" ^ strdescrs_name typ ^ "[0]), " ^ nest_descrs_name typ ^
           ", sizeof(" ^ nest_descrs_name typ ^
           ")/sizeof(" ^ nest_descrs_name typ ^ "[0]), "
           ^ "\"" ^ typ ^ "\");\n")::
          (if String.equal cond "" then [] else
             ["  map_set_entry_condition(ret->" ^ name ^ ", " ^ cond ^ ", ret);\n"])
        | Vector (typ, cap, cond) ->
          (if String.equal typ "uint32_t" then
             "  vector_set_layout(ret->" ^ name ^
             ", NULL, 0, NULL, 0, \"uint32_t\");\n"
           else
             "  vector_set_layout(ret->" ^ name ^ ", " ^
             strdescrs_name typ ^ ", sizeof(" ^ strdescrs_name typ ^
             ")/sizeof(" ^ strdescrs_name typ ^ "[0]), " ^ nest_descrs_name typ ^
             ", sizeof(" ^ nest_descrs_name typ ^
             ")/sizeof(" ^ nest_descrs_name typ ^ "[0]), " ^ "\"" ^ typ ^ "\");\n")::
          (if String.equal cond "" then [] else
             ["  vector_set_entry_condition(ret->" ^ name ^ ", " ^ cond ^ ", ret);\n"])
        | CHT (depth, height) ->
          ["  vector_set_layout(ret->" ^ name ^ ", NULL, 0, NULL, 0, \"uint32_t\");\n"]
        | DChain cap -> []
        | Int -> []
        | UInt -> []
        | UInt32 -> []
        | EMap (_, _, _, _) -> []
        | LPM cond ->
          (if String.equal cond "" then [] else
             ["  lpm_set_entry_condition(ret->" ^ name ^ ", " ^ cond ^ ");\n"])
     )
     containers []) ^
  "#endif//KLEE_VERIFICATION\n" ^
  "  allocated_nf_state = ret;\n" ^
  "  return ret;\n" ^
  "}\n"

let gen_inv_c_functions constraints containers =
  let transform_to_fields = function
    | Id "t" -> Some (Apply ("recent_time", []))
    | Id "v" -> None
    | Id "index" -> None
    | Id x -> Some (Str_idx ({v=Deref {v=Id "v";t=Unknown};
                              t=Unknown}, x))
    | _ -> None
  in
  (concat_flatten_map "\n"
     (fun (name, (cstruct_name, conditions)) ->
        match condition_kind containers name with
        | `Vector | `Map ->
          ["bool " ^ name ^ "(void* value, int index, void* state) {\n" ^
           (if cstruct_name = "uint32_t" then
              "  uint32_t v = *(uint32_t*)value;\n" else
              "  struct " ^ cstruct_name ^ " *v = value;\n") ^
           "  return " ^
           (concat_flatten_map " AND\n        "
              (fun term ->
                 let tterm = call_recursively_on_term transform_to_fields {t=Unknown;
                                                                           v=term} in
                 [render_tterm tterm])
              conditions []
           ) ^
           ";\n}"]
        | `LPM ->
          ["bool " ^ name ^ "(uint32_t prefix, int route) {\n" ^
           "  return " ^
           (concat_flatten_map " AND\n        "
              (fun term -> [render_term term])
              conditions []
           ) ^
           ";\n}"]
        | `Unknown -> ["unknown: " ^ name]
     ) constraints []
  )

let gen_entry_condition_decls containers =
  (concat_flatten_map ""
     (fun (name, cnt) ->
        match cnt with
        | Map (_, _, cond) -> if String.equal cond "" then [] else
            ["bool " ^ cond ^ "(void* key, int index);\n"]
        | Vector (_, _, cond) -> if String.equal cond "" then [] else
            ["bool " ^ cond ^ "(void* value, int index, void* state);\n"]
        | CHT (_, _) -> []
        | DChain _ -> []
        | Int -> []
        | UInt -> []
        | UInt32 -> []
        | EMap (_, _, _, _) -> []
        | LPM cond -> if String.equal cond "" then [] else
            ["bool " ^ cond ^ "(uint32_t prefix, int value);\n"]
     )
     containers [])

let gen_loop_iteration_border_call containers =
  "void nf_loop_iteration_border(unsigned lcore_id, vigor_time_t time) {\n" ^
  "  loop_iteration_border(" ^
  (concat_flatten_map ",\n                        "
     (fun (name, cnt) ->
        match cnt with
        | EMap (_, _, _, _) -> []
        | Map (_, _, _)
        | Vector (_, _, _)
        | CHT (_, _)
        | LPM _
        | DChain _ -> ["&allocated_nf_state->" ^ name]
        | _ -> ["allocated_nf_state->" ^ name]
     )
     containers ["lcore_id"; "time"]) ^
  ");\n}\n"

let () =
  let cout = open_out "loop.h" in
  fprintf cout "#ifndef _LOOP_H_INCLUDED_\n";
  fprintf cout "#define _LOOP_H_INCLUDED_\n";
  fprintf cout "#include \"libvig/verified/double-chain.h\"\n";
  fprintf cout "#include \"libvig/verified/map.h\"\n";
  fprintf cout "#include \"libvig/verified/vector.h\"\n";
  fprintf cout "#include \"libvig/verified/cht.h\"\n";
  fprintf cout "#include \"libvig/verified/lpm-dir-24-8.h\"\n";
  fprintf cout "#include \"libvig/proof/coherence.h\"\n";
  fprintf cout "#include \"libvig/verified/vigor-time.h\"\n";
  List.iter (fun incl ->
      fprintf cout "#include \"%s\"\n" incl;)
    !Nf_data_spec.gen_custom_includes;
  fprintf cout "%s\n" (gen_inv_conditions constraints containers);
  fprintf cout "%s\n" (gen_inv_lemmas containers);
  fprintf cout "%s\n" (gen_loop_invariant containers);
  fprintf cout "%s\n" (gen_invariant_consume_decl containers);
  fprintf cout "%s\n" (gen_invariant_produce_decl containers);
  fprintf cout "%s\n" (gen_loop_iteration_border_decl containers);
  fprintf cout "#endif//_LOOP_H_INCLUDED_\n";
  close_out cout;
  let cout = open_out "state.h" in
  fprintf cout "#ifndef _STATE_H_INCLUDED_\n";
  fprintf cout "#define _STATE_H_INCLUDED_\n";
  fprintf cout "#include \"loop.h\"\n";
  fprintf cout "%s\n" (gen_struct containers);
  fprintf cout "%s;\n" (gen_allocation_proto containers);
  fprintf cout "#endif//_STATE_H_INCLUDED_\n";
  close_out cout;
  let cout = open_out "loop.c" in
  fprintf cout "#include <klee/klee.h>\n";
  fprintf cout "#include \"loop.h\"\n";
  fprintf cout "#include \"libvig/models/verified/vigor-time-control.h\"\n";
  fprintf cout "#include \"libvig/models/verified/double-chain-control.h\"\n";
  fprintf cout "#include \"libvig/models/verified/map-control.h\"\n";
  fprintf cout "#include \"libvig/models/verified/vector-control.h\"\n";
  fprintf cout "%s\n" (gen_loop_reset_impl containers);
  fprintf cout "%s\n" (gen_loop_invariant_consume_stub containers);
  fprintf cout "%s\n" (gen_loop_invariant_produce_stub containers);
  fprintf cout "%s\n" (gen_loop_iteration_border_stub containers);
  close_out cout;
  let cout = open_out "state.c" in
  fprintf cout "#include \"state.h\"\n";
  fprintf cout "#include <stdlib.h>\n";
  fprintf cout "#include \"libvig/verified/boilerplate-util.h\"\n";
  fprintf cout "#ifdef KLEE_VERIFICATION\n";
  fprintf cout "#include \"libvig/models/verified/double-chain-control.h\"\n";
  fprintf cout "#include \"libvig/models/verified/ether.h\"\n";
  fprintf cout "#include \"libvig/models/verified/map-control.h\"\n";
  fprintf cout "#include \"libvig/models/verified/vector-control.h\"\n";
  fprintf cout "#include \"libvig/models/verified/lpm-dir-24-8-control.h\"\n";
  fprintf cout "#endif//KLEE_VERIFICATION\n";
  fprintf cout "struct State* allocated_nf_state = NULL;\n";
  fprintf cout "%s\n" (gen_inv_c_functions constraints containers);
  fprintf cout "%s\n" (gen_allocation containers);
  fprintf cout "#ifdef KLEE_VERIFICATION\n";
  fprintf cout "%s\n" (gen_loop_iteration_border_call containers);
  fprintf cout "#endif//KLEE_VERIFICATION\n";
  close_out cout;
