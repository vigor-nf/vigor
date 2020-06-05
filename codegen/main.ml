open Cil
open Printf
module F = Frontc
module E = Errormsg
module P = Pretty

let inductive_name compinfo = compinfo.cname ^ "i"
let predicate_name compinfo = compinfo.cname ^ "p"
let constructor_name compinfo = compinfo.cname ^ "c"
let lhash_name compinfo = "_" ^ compinfo.cname ^ "_hash"
let strdescrs_name compinfo = compinfo.cname ^ "_descrs"
let nest_descrs_name compinfo = compinfo.cname ^ "_nests"
let alloc_fun_name compinfo = compinfo.cname ^ "_allocate"
let eq_fun_name compinfo = compinfo.cname ^ "_eq"
let hash_fun_name compinfo = compinfo.cname ^ "_hash"
let log_fun_name compinfo = "LOG_" ^ (String.uppercase_ascii compinfo.cname)
(* let advance_time_lemma inv = "advance_time_" ^ inv
 * let init_inv_lemma inv = "init_" ^ inv *)
let default_name compinfo = "DEFAULT_" ^ (String.uppercase_ascii compinfo.cname)

let gen_inductive_type compinfo =
  "/*@\ninductive " ^ (inductive_name compinfo) ^
  " = " ^ (constructor_name compinfo) ^ "(" ^
  (String.concat ", " (List.map (fun {ftype;_} ->
       match ftype with
       | TComp (field_str, _) ->
         (inductive_name field_str)
       | TArray (field_t, Some (Const (CInt64 (c, _, _))), _) ->
         let rec csl_fields (c : int64) =
           if 1L < c then
             (P.sprint ~width:100 (d_type () field_t)) ^ ", " ^
             (csl_fields (Int64.sub c 1L))
           else if c = 1L then
             (P.sprint ~width:100 (d_type () field_t))
           else failwith "A 0-element array"
         in
         csl_fields c
       | TArray (field_t, _, _) ->
         failwith "An of unsupported array count " ^
         (P.sprint ~width:100 (d_type () ftype))
       | _ -> P.sprint ~width:100 (d_type () ftype)
     ) compinfo.cfields)) ^
  "); @*/"

let rec typ_to_ir_ttype = function
  | TVoid _ -> "Ir.Void"
  | TInt (ISChar, _)
  | TInt (IChar, _) -> "Ir.Sint8"
  | TInt (IUChar, _) -> "Ir.Uint8"
  | TInt (IShort, _) -> "Ir.Sint16"
  | TInt (IUShort, _) -> "Ir.Uint16"
  | TInt (ILong, _) -> "Ir.Sint64"
  | TInt (IULong, _) -> "Ir.Uint64"
  | TInt (ILongLong, _) -> "Ir.Sint64"
  | TInt (IULongLong, _) -> "Ir.Uint64"
  | TInt (IInt, _) -> "Ir.Sint32"
  | TInt (IUInt, _) -> "Ir.Uint32"
  | TFloat (_, _) -> "Float-not-supported"
  | TArray (_, _, _) -> "Array-not-supported"
  | TComp (_, _) -> "TComp-not-supported"
  | TNamed ({ttype;_}, _) -> typ_to_ir_ttype ttype
  | _ -> "Not supported Cil type"

let rec gen_fspec_record compinfo =
  "\"" ^ compinfo.cname ^
  "\", [" ^
  (String.concat "; " (List.map (fun {fname;ftype;_} ->
       let key = "\"" ^ fname ^ "\", " in
       match ftype with
       | TComp (field_str, _) ->
         key ^ "Ir.Str(" ^ (gen_fspec_record field_str) ^ ")"
       | TArray (field_t, Some (Const (CInt64 (_, _, _))), _) ->
         key ^ "Ir.Array (" ^ (typ_to_ir_ttype field_t) ^ ")"
       | TArray (field_t, _, _) ->
         failwith "An of unsupported array count " ^
         (P.sprint ~width:100 (d_type () ftype))
       | _ ->
         key ^ (typ_to_ir_ttype ftype)
     ) compinfo.cfields)) ^
  "]"

let rec gen_default_value compinfo =
  (constructor_name compinfo) ^ "(" ^
  (String.concat ", " (List.map (fun {ftype;_} ->
       match ftype with
       | TComp (field_str, _) ->
         (gen_default_value field_str)
       | TArray (field_t, Some (Const (CInt64 (c, _, _))), _) ->
         let rec csl_fields (c : int64) =
           if 1L < c then
             "0, " ^ (csl_fields (Int64.sub c 1L))
           else if 1L = c then
             "0"
           else failwith "A 0-element array"
         in
         (csl_fields c)
       | TArray (field_t, _, _) ->
         failwith "An array of unsupported count" ^
         (P.sprint ~width:100 (d_type () ftype))
       | _ -> "0"
     ) compinfo.cfields)) ^ ")"

let gen_default_value_macro compinfo =
  "#define " ^ (default_name compinfo) ^ " " ^ (gen_default_value compinfo)

let gen_predicate compinfo =
  "/*@\npredicate " ^ (predicate_name compinfo) ^ "(struct " ^
  compinfo.cname ^ "* ptr; " ^ (inductive_name compinfo) ^ " v) = \n" ^
  "  struct_" ^ compinfo.cname ^ "_padding(ptr) &*&\n" ^
  (String.concat " &*&\n" (List.map (fun {fname;ftype;_} ->
       match ftype with
       | TComp (field_str, _) ->
         "  " ^ (predicate_name field_str) ^ "(&ptr->" ^ fname ^ ", ?" ^
         fname ^ "_f)"
       | TArray (field_t, Some (Const (CInt64 (c, _, _))), _) ->
         let rec csl_fields (i : int64) =
           if 1L < i then
             "cons(?" ^ fname ^ "_" ^ (Int64.to_string (Int64.sub c i)) ^ ", " ^
             (csl_fields (Int64.sub i 1L)) ^ ")"
           else if i = 1L then
             "cons(?" ^ fname ^ "_" ^ (Int64.to_string (Int64.sub c i)) ^
             ", ?_nil)"
           else failwith "A 0-element array"
         in
         "  uchars(ptr->" ^ fname ^ ", " ^ (Int64.to_string c) ^
         ", ?" ^ fname ^ "_f) " ^
         "&*&\n  length(" ^ fname ^ "_f) == 6 " ^
         "&*&\n  " ^ fname ^ "_f == " ^ (csl_fields c) ^ " &*&\n" ^
         "  switch(_nil) { case nil: return true; case cons(nh, nt): return false; }"
       | TArray (field_t, _, _) ->
         failwith "An of unsupported array count " ^
         (P.sprint ~width:100 (d_type () ftype))
       | _ -> "  ptr->" ^ fname ^ " |-> ?" ^ fname ^ "_f"
     ) compinfo.cfields)) ^
   " &*&\n  v == " ^ (constructor_name compinfo) ^ "(" ^
  (String.concat ", " (List.map (fun {fname;ftype;_} ->
       match ftype with
       | TArray (field_t, Some (Const (CInt64 (c, _, _))), _) ->
         let rec csl_fields (i : int64) =
           if 1L < i then
             fname ^ "_" ^ (Int64.to_string (Int64.sub c i)) ^ ", " ^
             (csl_fields (Int64.sub i 1L))
           else if i = 1L then
             fname ^ "_" ^ (Int64.to_string (Int64.sub c i))
           else failwith "A 0-element array"
         in
         csl_fields c
       | TArray (field_t, _, _) ->
         failwith "An of unsupported array count " ^
         (P.sprint ~width:100 (d_type () ftype))
       | _ -> fname ^ "_f"
     ) compinfo.cfields)) ^
  "); @*/"


let eq_fun_contract compinfo =
  "//@ requires [?f1]" ^ (predicate_name compinfo) ^ "(a, ?aid) &*& " ^
  "[?f2]" ^ (predicate_name compinfo) ^ "(b, ?bid);\n" ^
  "/*@ ensures [f1]" ^ (predicate_name compinfo) ^ "(a, aid) &*& " ^
  "[f2]" ^ (predicate_name compinfo) ^ "(b, bid) &*&\n" ^
  "            (result ? aid == bid : aid != bid); @*/"

let gen_eq_function compinfo =
  "bool " ^ (eq_fun_name compinfo) ^
  "(void* a, void* b)\n" ^
  (eq_fun_contract compinfo) ^ "\n" ^
  "{\n  struct " ^ compinfo.cname ^
  "* id1 = (struct " ^ compinfo.cname ^ "*) a;\n  struct " ^ compinfo.cname ^
  "* id2 = (struct " ^ compinfo.cname ^ "*) b;\n" ^
  "  //@ open [f1]" ^ (predicate_name compinfo) ^ "(a, aid);\n" ^
  "  //@ open [f2]" ^ (predicate_name compinfo) ^ "(b, bid);\n" ^
  let field_eq_name fname = fname ^ "_eq" in
  (String.concat "" (List.map (fun {fname;ftype;_} ->
       match ftype with
       | TComp (field_str, _) ->
         "  bool " ^ (field_eq_name fname) ^ " = " ^
         (eq_fun_name field_str) ^ "(&id1->" ^ fname ^ ", &id2->" ^ fname ^ ");\n"
       | _ -> ""
     ) compinfo.cfields)) ^
  "  return " ^
  (String.concat "\n     AND " (List.map (fun {fname;ftype;_} ->
       match ftype with
       | TComp (field_str, _) ->
         (field_eq_name fname)
       | TArray (field_t, Some (Const (CInt64 (c, _, _))), _) ->
         let rec arr_fields (i : int64) =
           let current = (Int64.to_string (Int64.sub c i)) in
           if 1L < i then
             "(id1->" ^ fname ^ "[" ^ current ^ "] == " ^
             "id2->" ^ fname ^ "[" ^ current ^ "])\n     AND " ^
             (arr_fields (Int64.sub i 1L))
           else if i = 1L then
             "(id1->" ^ fname ^ "[" ^ current ^ "] == " ^
             "id2->" ^ fname ^ "[" ^ current ^ "])"
           else failwith "A 0-element array"
         in
         arr_fields c
       | TArray (field_t, _, _) ->
         failwith "An of unsupported array count " ^
         (P.sprint ~width:100 (d_type () ftype))
       | _ -> "(id1->" ^ fname ^ " == id2->" ^ fname ^ ")"
     ) compinfo.cfields)) ^
  ";\n" ^
  "  //@ close [f1]" ^ (predicate_name compinfo) ^ "(a, aid);\n" ^
  "  //@ close [f2]" ^ (predicate_name compinfo) ^ "(b, bid);\n" ^
  "\n}\n"

let gen_eq_function_decl compinfo =
  "bool " ^ (eq_fun_name compinfo) ^ "(void* a, void* b);\n" ^
  (eq_fun_contract compinfo)


let gen_logical_hash compinfo =
  let field_name fname = fname ^ "_f" in
  let rec cutoff ftype =
    match ftype with
    | TInt (ILong, _)
    | TInt (IULong, _)
    | TInt (ILongLong, _)
    | TInt (IULongLong, _) ->
      " & 0xffffffff"
    | TNamed (tinfo,_) -> cutoff tinfo.ttype
    | _ -> ""
  in
  let rec basic_hash fname ftype =
    match ftype with
    | TInt (ILong, _)
    | TInt (IULong, _)
    | TInt (ILongLong, _)
    | TInt (IULongLong, _) ->
      (* Take only the least signigicant 44 bits,
         to make sure it fits in uint64_t*)
      "(" ^ fname ^ "&0xfffffffffff)"
    | TInt (IChar, _)
    | TInt (ISChar, _)
    | TInt (IShort, _)
    | TInt (IInt, _)
    | TInt (IUChar, _)
    | TInt (IBool, _)
    | TInt (IUShort, _)
    | TInt (IUInt, _) -> fname
    | TNamed (tinfo,_) -> basic_hash fname tinfo.ttype
    | _ -> "<unsupported field type>"
  in
  let field_hash field =
    match field with
    | {ftype=TComp (field_str,_);fname;_} ->
         (lhash_name field_str) ^ "(" ^ (field_name fname) ^ ")"
    | {ftype=TArray (field_t, Some (Const (CInt64 (c, _, _))), _);fname;_} ->
      let rec arr_fields (i : int64) =
        if 1L < i then
          "crc32_hash(" ^ (arr_fields (Int64.sub i 1L)) ^ ", "
          ^ (basic_hash (fname ^ "_" ^ (Int64.to_string (Int64.sub i 1L)))
               field_t) ^ ")"
        else if i = 1L then
          fname ^ "_0"
        else failwith "A 0-element array"
      in
      arr_fields c
    | {ftype=TArray (field_t, _, _);_} ->
      failwith "An of unsupported array count " ^
      (P.sprint ~width:100 (d_type () field.ftype))
    | {fname;ftype;_} -> (basic_hash (field_name fname) ftype)
  in
  let field_hash_0 field =
    match field with
    | {ftype=TComp (field_str,_);fname;_} ->
      "crc32_hash(0, " ^ (lhash_name field_str) ^
      "(" ^ (field_name fname) ^ "))"
    | {ftype=TArray (field_t, Some (Const (CInt64 (c, _, _))), _);fname;_} ->
      let rec arr_fields (i : int64) =
        if 1L < i then
          "crc32_hash(" ^ (arr_fields (Int64.sub i 1L)) ^ ", "
          ^ (basic_hash (fname ^ "_" ^ (Int64.to_string (Int64.sub i 1L)))
               field_t) ^ ")"
        else if i = 1L then
          "crc32_hash(0, " ^ fname ^ "_0)"
        else failwith "A 0-element array"
      in
      arr_fields c
    | {ftype=TArray (field_t, _, _);_} ->
      failwith "An of unsupported array count " ^
      (P.sprint ~width:100 (d_type () field.ftype))
    | {fname;ftype;_} -> "crc32_hash(0, " ^
                         (basic_hash (field_name fname) ftype) ^ ")" ^
                         (cutoff ftype)
  in
  let rec gen_exp_r fields acc =
    match fields with
    | hd::tl -> gen_exp_r tl ("crc32_hash(" ^ acc ^ ", " ^
                              (field_hash hd) ^ ")" ^
                              (cutoff hd.ftype))
    | [] -> acc
  in
  let gen_exp fields =
    match fields with
    | hd::tl -> gen_exp_r tl (field_hash_0 hd)
    | [] -> "0"
  in
  "/*@\nfixpoint unsigned " ^ (lhash_name compinfo) ^ "(" ^
  (inductive_name compinfo) ^ " x) {\n  switch(x)" ^
  " { case " ^ (constructor_name compinfo) ^ "(" ^
  (String.concat ", " (List.map (fun {fname;ftype;_} ->
       match ftype with
       | TArray (field_t, Some (Const (CInt64 (c, _, _))), _) ->
         let rec csl_fields (i : int64) =
           if 1L < i then
             fname ^ "_" ^ (Int64.to_string (Int64.sub c i)) ^
             ", " ^ (csl_fields (Int64.sub i 1L))
           else if i = 1L then
             fname ^ "_" ^ (Int64.to_string (Int64.sub c i))
           else failwith "A 0-element array"
         in
         csl_fields c
       | TArray (field_t, _, _) ->
         failwith "An of unsupported array count " ^
         (P.sprint ~width:100 (d_type () ftype))
       | _ -> fname ^ "_f"
     ) compinfo.cfields)) ^ "):\n" ^
  "    return " ^ (gen_exp compinfo.cfields) ^
  ";\n  }\n} @*/"

let hash_contract compinfo =
  "//@ requires [?f]" ^ (predicate_name compinfo) ^ "(obj, ?v);\n" ^
  "//@ ensures [f]" ^ (predicate_name compinfo) ^
  "(obj, v) &*& result == " ^ (lhash_name compinfo) ^ "(v);"

let gen_hash compinfo =
  let rec basic_hash fname ftype =
    match ftype with
    | TInt (ILong, _)
    | TInt (IULong, _)
    | TInt (ILongLong, _)
    | TInt (IULongLong, _) ->
      (* Take only the least signigicant 44 bits,
         to make sure it fits in uint64_t*)
      "(unsigned int)(__builtin_ia32_crc32di(hash, (unsigned long long)(" ^
      fname ^ "&0xfffffffffff))&0xffffffff)"
    | TInt (IChar, _)
    | TInt (IBool, _)
    | TInt (IUChar, _)
    | TInt (ISChar, _)
    | TInt (IUShort, _)
    | TInt (IShort, _)
    | TInt (IUInt, _)
    | TInt (IInt, _) -> (* peel off the sign bit*)
      "__builtin_ia32_crc32si(hash, " ^ fname ^ ")"
    | TNamed (tinfo,_) -> basic_hash fname tinfo.ttype
    | _ -> "<unsupported field type>"
  in
  "unsigned " ^ (hash_fun_name compinfo) ^ "(void* obj)\n" ^
  (hash_contract compinfo) ^ "\n" ^
  "{\n" ^
  "  struct " ^ compinfo.cname ^ "* id = (struct " ^ compinfo.cname ^
  "*) obj;\n" ^
  "\n" ^
  "  //@ open [f]" ^ (predicate_name compinfo) ^ "(obj, v);\n" ^
  (String.concat "" (List.map (fun {fname;ftype;_} ->
       match ftype with
       | TArray (field_t, Some (Const (CInt64 (c, _, _))), _) ->
         let rec arr_fields (i : int64) =
           let current = (Int64.to_string (Int64.sub c i)) in
           let curr_field = fname ^ "_" ^ current in
           if 0L < i then
             "  " ^ (P.sprint ~width:100 (d_type () field_t)) ^
             curr_field ^ " = " ^
             "id->" ^ fname ^ "[" ^ current ^ "];\n" ^
             "  //@ produce_limits(" ^ curr_field ^ ");\n" ^
             (arr_fields (Int64.sub i 1L))
           else ""
         in
         arr_fields c
       | TArray (field_t, _, _) ->
         failwith "An of unsupported array count " ^
         (P.sprint ~width:100 (d_type () ftype))
       | _ -> ""
     ) compinfo.cfields)) ^
  "  //@ close [f]" ^ (predicate_name compinfo) ^ "(obj, v);\n" ^
  "\n" ^
  "  unsigned hash = 0;\n" ^
  (String.concat "" (List.map (fun {fname;ftype;_} ->
       match ftype with
       | TComp (field_str,_) ->
         "  unsigned " ^ fname ^ "_hash = " ^
         (hash_fun_name field_str) ^ "(&id->" ^ fname ^ ");\n" ^
         "  hash = __builtin_ia32_crc32si(hash, " ^ fname ^ "_hash);\n"
       | TArray (field_t, Some (Const (CInt64 (c, _, _))), _) ->
         let rec arr_fields (i : int64) =
           let current = (Int64.to_string (Int64.sub c i)) in
           let curr_field = fname ^ "_" ^ current in
           if 1L <= i then
             "  hash = " ^ (basic_hash curr_field field_t) ^ ";\n"
               ^ (arr_fields (Int64.sub i 1L))
           else ""
         in
         arr_fields c
       | _ ->
         "  hash = " ^ (basic_hash ("id->" ^ fname) ftype) ^ ";\n"
     ) compinfo.cfields)) ^
  "  return hash;\n" ^
  "}"

let gen_hash_dummy compinfo =
  let strdescrs = (strdescrs_name compinfo) in
  let nests = (nest_descrs_name compinfo) in
  "unsigned " ^ (hash_fun_name compinfo) ^ "(void* obj)\n" ^
  "{\n" ^
  "  klee_trace_ret();\n" ^
  "  klee_trace_param_tagged_ptr(obj, sizeof(struct " ^ compinfo.cname ^ "),\n" ^
  "                             \"obj\", \"" ^ compinfo.cname ^
  "\", TD_BOTH);\n" ^
  "  for (int i = 0; i < sizeof(" ^ strdescrs ^ ")/" ^
  "sizeof(" ^ strdescrs ^ "[0]); ++i) {\n" ^
  "    klee_trace_param_ptr_field_arr_directed(obj,\n" ^
  "                                            " ^ strdescrs ^ "[i].offset,\n" ^
  "                                            " ^ strdescrs ^ "[i].width,\n" ^
  "                                            " ^ strdescrs ^ "[i].count,\n" ^
  "                                            " ^ strdescrs ^ "[i].name,\n" ^
  "                                            TD_BOTH);\n" ^
  "  }" ^
  "  for (int i = 0; i < sizeof(" ^ nests ^ ")/" ^
  "sizeof(" ^ nests ^ "[0]); ++i) {\n" ^
  "    klee_trace_param_ptr_nested_field_arr_directed(obj,\n" ^
  "                                                  " ^ nests ^ "[i].base_offset,\n" ^
  "                                                  " ^ nests ^ "[i].offset,\n" ^
  "                                                  " ^ nests ^ "[i].width,\n" ^
  "                                                  " ^ nests ^ "[i].count,\n" ^
  "                                                  " ^ nests ^ "[i].name,\n" ^
  "                                                  TD_BOTH);\n" ^
  "  }" ^
  "  return klee_int(\"" ^ compinfo.cname ^ "_hash\");" ^
  "}"

let gen_hash_decl compinfo =
  "unsigned " ^ (hash_fun_name compinfo) ^ "(void* obj);\n" ^
  (hash_contract compinfo)

let alloc_fun_contract compinfo =
  "//@ requires chars(obj, sizeof(struct " ^ compinfo.cname ^
  "), _);\n" ^
  "//@ ensures " ^ (predicate_name compinfo) ^
  "(obj, " ^ (default_name compinfo) ^ ");"

let gen_alloc_function compinfo =
  "void " ^ (alloc_fun_name compinfo) ^ "(void* obj)\n" ^
  (alloc_fun_contract compinfo) ^ "\n" ^
  "{\n" ^
  "  //@ close_struct((struct " ^ compinfo.cname ^ "*) obj);\n" ^
  "  struct " ^ compinfo.cname ^
  "* id = (struct " ^ compinfo.cname ^ "*) obj;\n" ^
  let rec zero_fields cstruct name field_name accessor =
    (String .concat "\n" (List.map (fun {fname;ftype;_} ->
         let field_id = name ^ accessor ^ fname in
         match ftype with
         | TComp (field_str, _) ->
           (zero_fields field_str field_id fname ".")
         | TArray (field_t, Some (Const (CInt64 (c, _, _))), _) ->
           let rec arr_fields (i : int64) =
           let current = (Int64.to_string (Int64.sub c i)) in
             if 0L < i then
               "  " ^ field_id ^ "[" ^ current ^ "] = 0;\n" ^
               (arr_fields (Int64.sub i 1L))
             else ""
           in
           let rec arr_switch tail (i : int64) =
           let current = (Int64.to_string (Int64.sub c i)) in
             if 0L < i then
               "  switch(" ^ tail ^
               ") { case cons(h" ^ current ^ ", t" ^ current ^ "):\n" ^
               (arr_switch ("t" ^ current) (Int64.sub i 1L)) ^
               "\n  case nil: assert false;\n }"
             else ""
           in
           "//@ assert " ^ field_id ^ "[0.." ^ (Int64.to_string c) ^ "] |-> ?" ^
           field_name ^ "_" ^ fname ^ "_lst;\n" ^
           "/*@ " ^ arr_switch (field_name ^ "_" ^ fname ^ "_lst") c ^ "@*/\n" ^
           arr_fields c
         | TArray (field_t, _, _) ->
           failwith "An of unsupported array count " ^
           (P.sprint ~width:100 (d_type () ftype))
         | _ -> "  " ^ field_id ^ " = 0;"
       ) cstruct.cfields))
  in
  (zero_fields compinfo "id" "id" "->") ^ "\n" ^
  "  //@ close " ^ (predicate_name compinfo) ^ "(obj, " ^ (default_name compinfo) ^ ");\n" ^
  "}\n"

let gen_alloc_function_decl compinfo =
  "void " ^ (alloc_fun_name compinfo) ^ "(void* obj);\n" ^
  (alloc_fun_contract compinfo)

let gen_str_field_descrs compinfo =
  "struct str_field_descr " ^ (strdescrs_name compinfo) ^ "[] = {\n" ^
  (String.concat "\n" (List.map (fun {fname;ftype;_} ->
       match ftype with
       | TArray (field_t, Some (Const (CInt64 (c, _, _))), _) ->
         "  {offsetof(struct " ^ compinfo.cname ^
         ", " ^ fname ^ "), sizeof(" ^
         (P.sprint ~width:100 (d_type () field_t)) ^
         "), " ^ (Int64.to_string c) ^ ", \"" ^ fname ^ "\"},"
       | TArray (field_t, _, _) ->
         failwith "An of unsupported array count " ^
         (P.sprint ~width:100 (d_type () ftype))
       | _ ->
         "  {offsetof(struct " ^ compinfo.cname ^
         ", " ^ fname ^ "), sizeof(" ^
         (P.sprint ~width:100 (d_type () ftype)) ^
         "), 0, \"" ^ fname ^ "\"},"
     ) compinfo.cfields)) ^
  "\n};\n" ^
  "struct nested_field_descr " ^ (nest_descrs_name compinfo) ^ "[] = {\n" ^
  (String.concat "" (List.map (fun {fname;ftype;_} ->
       match ftype with
       | TComp (nest_str, _) ->
         (String.concat "\n" (List.map (fun {fname=ffname;ftype=fftype;_} ->
              match fftype with
              | TArray (field_t, Some (Const (CInt64 (c, _, _))), _) ->
                "  {offsetof(struct " ^ compinfo.cname ^ ", " ^
                fname ^ "), offsetof(" ^ (P.sprint ~width:100 (d_type () ftype)) ^
                ", " ^ ffname ^ "), sizeof(" ^
                (P.sprint ~width:100 (d_type () field_t)) ^
                "), " ^ (Int64.to_string c) ^ ", \"" ^ ffname ^ "\"},"
              | TArray (field_t, _, _) ->
                failwith "An unsupported array count " ^
                (P.sprint ~width:100 (d_type () field_t))
              | _ ->
                "  {offsetof(struct " ^ compinfo.cname ^ ", " ^
                fname ^ "), offsetof(" ^ (P.sprint ~width:100 (d_type () ftype)) ^
                ", " ^ ffname ^ "), sizeof(" ^
                (P.sprint ~width:100 (d_type () fftype)) ^
                "), 0, \"" ^ ffname ^ "\"},"
            ) nest_str.cfields))
       | _ -> ""
     ) compinfo.cfields)) ^
  "\n};"

let gen_str_field_descrs_decl compinfo =
  let nested_descrs_count =
    (List.fold_left (fun count {ftype;_} ->
       match ftype with
       | TComp (nest_str, _) ->
         (List.length nest_str.cfields) + count
       | _ -> count
     ) 0 compinfo.cfields)
  in
  "extern struct str_field_descr " ^ (strdescrs_name compinfo) ^
  "[" ^ (string_of_int (List.length compinfo.cfields)) ^ "];\n" ^
  "extern struct nested_field_descr " ^ (nest_descrs_name compinfo) ^
  "[" ^ (string_of_int nested_descrs_count) ^ "];"

let gen_log_fun_decl compinfo =
  "#define " ^ (log_fun_name compinfo) ^ "(obj, p); \\\n" ^
  "  p(\"{\"); \\\n" ^
  (String.concat "\n" (List.map (fun {fname;ftype;_} ->
       match ftype with
       | TComp (nest_str, _) ->
         "  p(\"" ^ fname ^ ":\"); \\\n" ^
         "  " ^ (log_fun_name nest_str) ^ "(&(obj)->" ^ fname ^ "); \\"
       | TArray (field_t, Some (Const (CInt64 (c, _, _))), _) ->
         let rec arr_fields (i : int64) =
           let current = (Int64.to_string (Int64.sub c i)) in
           if 0L < i then
             "  p(\"" ^ fname ^ "[" ^ current ^ "]: %d\", (obj)->" ^
             fname ^ "[" ^ current ^ "]" ^ "); \\\n" ^
             (arr_fields (Int64.sub i 1L))
           else ""
         in
         arr_fields c
       | TArray (field_t, _, _) ->
         failwith "An of unsupported array count " ^
         (P.sprint ~width:100 (d_type () ftype))
       | _ ->
         "  p(\"" ^ fname ^ ": %d\", (obj)->" ^ fname ^ "); \\"
     ) compinfo.cfields)) ^ "\n" ^
  "  p(\"}\");\n"


let fill_impl_file compinfo impl_fname header_fname =
  let cout = open_out impl_fname in
  ignore (P.fprintf cout "#include \"%s\"\n\n" header_fname);
  ignore (P.fprintf cout "#include <stdint.h>\n\n");
  ignore (P.fprintf cout "%s\n\n" (gen_eq_function compinfo));
  ignore (P.fprintf cout "%s\n\n" (gen_alloc_function compinfo));
  ignore (P.fprintf cout "#ifdef KLEE_VERIFICATION\n");
  ignore (P.fprintf cout "%s\n" (gen_str_field_descrs compinfo));
  ignore (P.fprintf cout "%s\n\n" (gen_hash_dummy compinfo));
  ignore (P.fprintf cout "#else//KLEE_VERIFICATION\n\n");
  ignore (P.fprintf cout "%s\n\n" (gen_hash compinfo));
  ignore (P.fprintf cout "#endif//KLEE_VERIFICATION\n\n");
  close_out cout;
  ()

let gen_include_deps compinfo def_headers =
  (String.concat "" (List.map (fun {fname;ftype;_} ->
       match ftype with
       | TComp (nest_str, _) ->
         begin try let header_name = List.assoc nest_str.cname def_headers in
             "#include \"" ^ header_name ^ "\"\n"
         with Not_found -> "" end
       | _ -> ""
     ) compinfo.cfields))

let fill_header_file compinfo header_fname orig_fname def_headers =
  let cout = open_out header_fname in
  ignore (P.fprintf cout "#ifndef _%s_GEN_H_INCLUDED_\n" compinfo.cname);
  ignore (P.fprintf cout "#define _%s_GEN_H_INCLUDED_\n\n" compinfo.cname);
  ignore (P.fprintf cout "#include <stdbool.h>\n");  
  ignore (P.fprintf cout "#include \"libvig/verified/boilerplate-util.h\"\n\n");
  ignore (P.fprintf cout "#include \"libvig/verified/ether.h\"\n\n");
  ignore (P.fprintf cout "%s\n" (gen_include_deps compinfo def_headers));
  ignore (P.fprintf cout "#include \"%s\"\n\n" orig_fname);
  ignore (P.fprintf cout "%s\n\n" (gen_default_value_macro compinfo));
  ignore (P.fprintf cout "%s\n\n" (gen_inductive_type compinfo));
  ignore (P.fprintf cout "%s\n\n" (gen_predicate compinfo));
  ignore (P.fprintf cout "%s\n\n" (gen_logical_hash compinfo));
  ignore (P.fprintf cout "%s\n\n" (gen_hash_decl compinfo));
  ignore (P.fprintf cout "%s\n\n" (gen_eq_function_decl compinfo));
  ignore (P.fprintf cout "%s\n\n" (gen_alloc_function_decl compinfo));
  ignore (P.fprintf cout "%s\n\n" (gen_log_fun_decl compinfo));
  ignore (P.fprintf cout "#ifdef KLEE_VERIFICATION\n");
  ignore (P.fprintf cout "#  include <klee/klee.h>\n");
  ignore (P.fprintf cout "#  include \"libvig/models/str-descr.h\"\n\n");
  ignore (P.fprintf cout "%s\n" (gen_str_field_descrs_decl compinfo));
  ignore (P.fprintf cout "#endif//KLEE_VERIFICATION\n\n");
  ignore (P.fprintf cout "#endif//_%s_GEN_H_INCLUDED_\n" compinfo.cname);
  close_out cout;
  ()

let relativise_header_path fpath =
  let upper_dirs = Str.regexp ".*/libvig/" in
  Str.replace_first upper_dirs "libvig/" fpath

(* I can't believe OCaml doesn't have a string contains... from https://stackoverflow.com/a/8373836 *)
let contains s1 s2 =
    let re = Str.regexp_string s2
    in
        try ignore (Str.search_forward re s1 0); true
        with Not_found -> false

let fill_fspec_file header_fname compinfo fspec_fname =
  let cout = open_out_gen [Open_append] 0 fspec_fname in
  ignore (P.fprintf cout "let () = \n  \
                          gen_records := \
                          (\"%s\", (Ir.Str (%s)))::!gen_records\n\n"
            compinfo.cname (gen_fspec_record compinfo));
  ignore (P.fprintf cout "let () = \n  \
                          gen_custom_includes := \
                          \"%s\"::!gen_custom_includes\n\n"
            header_fname);
  close_out cout;
  ()

let traverse_globals (f : file) : unit =
  let def_headers = ref [] in
  List.iter (fun g ->
    match g with
    (* don't try to generate dpdk or libc headers *)
    | GCompTag (_, loc) when contains loc.file "dpdk/rte_" -> ()
    | GCompTag (_, loc) when contains loc.file "/usr/lib" -> ()
    | GCompTag (_, loc) when contains loc.file "/usr/include" -> ()
    | GCompTag (ifo, loc) ->
      let header_fname = loc.file ^ ".gen.h" in
      let impl_fname = loc.file ^ ".gen.c" in
      def_headers := (ifo.cname, (relativise_header_path header_fname))::
                     !def_headers;
      fill_header_file ifo header_fname
        (relativise_header_path loc.file) !def_headers;
      fill_impl_file ifo impl_fname (relativise_header_path header_fname);
      fill_fspec_file header_fname ifo "fspec_gen.ml";
      ()
    | _ -> ())
  f.globals


let parseOneFile (fname: string) : file =
  let cabs, cil = F.parse_with_cabs fname () in
  (* Rmtmps.removeUnusedTemps cil; *)
  cil

let processOneFile (cil: file) : unit =
  traverse_globals cil;
;;

let main () =
  print_CIL_Input := true;
  insertImplicitCasts := false;
  lineLength := 100000;
  warnTruncate := false;
  E.colorFlag := true;
  Cabs2cil.doCollapseCallCast := true;
  let usageMsg = "Usage: main.byte [options] source-files" in
  Arg.parse [] Ciloptions.recordFile usageMsg;
  Ciloptions.fileNames := List.rev !Ciloptions.fileNames;
  let files = List.map parseOneFile !Ciloptions.fileNames in
  let one =
    match files with
	  | [] -> E.s (E.error "No file names provided")
    | [o] -> o
    | _ -> Mergecil.merge files "stdout"
  in

  processOneFile one
;;


begin
  try
    main ()
  with
  | F.CabsOnly -> ()
  | E.Error -> ()
end;
exit (if !E.hadErrors then 1 else 0)

