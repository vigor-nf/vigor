open Cil
module F = Frontc
module E = Errormsg
module P = Pretty

let inductive_name compinfo = compinfo.cname ^ "i"
let predicate_name compinfo = compinfo.cname ^ "p"
let constructor_name compinfo = compinfo.cname ^ "c"
let lhash_name compinfo = "_" ^ compinfo.cname ^ "_hash"
let strdescrs_name compinfo = compinfo.cname ^ "_descrs"
let alloc_fun_name compinfo = compinfo.cname ^ "_allocate"
let eq_fun_name compinfo = compinfo.cname ^ "_eq"
let hash_fun_name compinfo = compinfo.cname ^ "_hash"
let log_fun_name compinfo = "log_" ^ compinfo.cname

let gen_inductive_type compinfo =
  "/*@\ninductive " ^ (inductive_name compinfo) ^
  " = " ^ (constructor_name compinfo) ^ "(" ^
  (String.concat ", " (List.map (fun {ftype;_} ->
       P.sprint ~width:100 (d_type () ftype)
     ) compinfo.cfields)) ^
  "); @*/"

let gen_predicate compinfo =
  "/*@\npredicate " ^ (predicate_name compinfo) ^ "(struct " ^
  compinfo.cname ^ "* ptr; " ^ (inductive_name compinfo) ^ " v) = \n" ^
  "  struct_" ^ compinfo.cname ^ "_padding(ptr) &*&\n" ^
  (String.concat " &*&\n" (List.map (fun {fname;_} ->
       "  ptr->" ^ fname ^ " |-> ?" ^ fname ^ "_f"
     ) compinfo.cfields)) ^
   " &*&\n  v == " ^ (constructor_name compinfo) ^ "(" ^
  (String.concat ", " (List.map (fun {fname;_} ->
       fname ^ "_f"
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
  "* id1 = a;\n  struct " ^ compinfo.cname ^
  "* id2 = b;\n  return " ^
  (String.concat "\n     AND " (List.map (fun {fname;_} ->
       "id1->" ^ fname ^ " == id2->" ^ fname) compinfo.cfields)) ^
  ";\n}\n"

let gen_eq_function_decl compinfo =
  "bool " ^ (eq_fun_name compinfo) ^ "(void* a, void* b);\n" ^
  (eq_fun_contract compinfo)


let gen_logical_hash compinfo =
  let rec gen_exp_r fields acc =
    match fields with
    | hd::tl -> gen_exp_r tl ("(" ^ acc ^ " * 31 + " ^ hd.fname ^ "_f)")
    | [] -> acc
  in
  let gen_exp fields =
    match fields with
    | hd::tl -> gen_exp_r tl (hd.fname ^ "_f")
    | [] -> "(0)"
  in
  "/*@\nfixpoint unsigned " ^ (lhash_name compinfo) ^ "(" ^
  (inductive_name compinfo) ^ " x) {\n  switch(x)" ^
  " { case " ^ (constructor_name compinfo) ^ "(" ^
  (String.concat ", " (List.map (fun {fname;_} ->
       fname ^ "_f"
     ) compinfo.cfields)) ^ "):\n" ^
  "return _wrap" ^ (gen_exp compinfo.cfields) ^
  ";\n  }\n} @*/"

let hash_contract compinfo =
  "//@ requires [?f]" ^ (predicate_name compinfo) ^ "(obj, ?v);\n" ^
  "//@ ensures [f]" ^ (predicate_name compinfo) ^
  "(obj, v) &*& result == " ^ (lhash_name compinfo) ^ "(v);"

let gen_hash compinfo =
  "unsigned " ^ (hash_fun_name compinfo) ^ "(void* obj)\n" ^
  (hash_contract compinfo) ^ "\n" ^
  "{\n" ^
  "  struct " ^ compinfo.cname ^ "* id = obj;\n" ^
  "  unsigned long long hash = 0;\n" ^
  (String.concat "  hash *= 31;\n" (List.map (fun {fname;_} ->
       "  hash += id->" ^ fname ^ ";\n"
     ) compinfo.cfields)) ^
  "  hash = wrap(hash);\n" ^
  "  return (unsigned) hash;\n" ^
  "}"

let gen_hash_decl compinfo =
  "unsigned " ^ (hash_fun_name compinfo) ^ "(void* obj);\n" ^
  (hash_contract compinfo)

let alloc_fun_contract compinfo =
  "//@ requires chars(obj, sizeof(struct " ^ compinfo.cname ^
  "), _);\n" ^
  "//@ ensures " ^ (predicate_name compinfo) ^ "(obj, _);"

let gen_alloc_function compinfo =
  "void " ^ (alloc_fun_name compinfo) ^ "(void* obj)\n" ^
  (alloc_fun_contract compinfo) ^ "\n" ^
  "{\n" ^
  "  IGNORE(obj);\n" ^
  "  //@ close_struct((struct " ^ compinfo.cname ^ "*) obj);\n" ^
  "  //@ close " ^ (predicate_name compinfo) ^ "(obj, _);\n" ^
  "}"

let gen_alloc_function_decl compinfo =
  "void " ^ (alloc_fun_name compinfo) ^ "(void* obj);\n" ^
  (alloc_fun_contract compinfo)

let gen_str_field_descrs compinfo =
  "struct str_field_descr " ^ (strdescrs_name compinfo) ^ "[] = {\n" ^
  (String.concat "\n" (List.map (fun {fname;ftype;_} ->
       "  {offsetof(struct " ^ compinfo.cname ^
       ", " ^ fname ^ "), sizeof(" ^
       (P.sprint ~width:100 (d_type () ftype)) ^
       "), 0, \"" ^ fname ^ "\"},"
     ) compinfo.cfields)) ^
  "\n};"

let gen_str_field_descrs_decl compinfo =
  "extern struct str_field_descr " ^ (strdescrs_name compinfo) ^
  "[" ^ (string_of_int (List.length compinfo.cfields)) ^ "];"

let gen_log_fun_decl compinfo =
  "void " ^ (log_fun_name compinfo) ^ "(struct " ^ compinfo.cname ^ "* obj);"

let gen_log_fun compinfo =
  "void " ^ (log_fun_name compinfo) ^ "(struct " ^ compinfo.cname ^ "* obj)\n" ^
  "{\n" ^
  "  NF_DEBUG(\"{\");\n" ^
  (String.concat "\n" (List.map (fun {fname;_} ->
       "  NF_DEBUG(\"" ^ fname ^ ": %d\", obj->" ^ fname ^ ");"
     ) compinfo.cfields)) ^ "\n" ^
  "  NF_DEBUG(\"}\");\n" ^
  "}"

let gen_log_fun_dummy compinfo =
  "void " ^ (log_fun_name compinfo) ^ "(struct " ^ compinfo.cname ^ "* obj)\n" ^
  "{\n  IGNORE(obj);\n}"



let fill_impl_file compinfo impl_fname header_fname =
  let cout = open_out impl_fname in
  P.fprintf cout "#include \"%s\"\n\n" header_fname;
  P.fprintf cout "%s\n\n" (gen_hash compinfo);
  P.fprintf cout "%s\n\n" (gen_eq_function compinfo);
  P.fprintf cout "%s\n\n" (gen_alloc_function compinfo);
  P.fprintf cout "#ifdef KLEE_VERIFICATION\n";
  P.fprintf cout "%s\n" (gen_str_field_descrs compinfo);
  P.fprintf cout "#endif//KLEE_VERIFICATION\n\n";
  P.fprintf cout "#ifdef ENABLE_LOG\n";
  P.fprintf cout "#include \"lib/nf_log.h\"\n";
  P.fprintf cout "%s\n\n" (gen_log_fun compinfo);
  P.fprintf cout "#else//ENABLE_LOG\n";
  P.fprintf cout "%s\n" (gen_log_fun_dummy compinfo);
  P.fprintf cout "#endif//ENABLE_LOG\n\n";
  close_out cout;
  ()

let fill_header_file compinfo header_fname orig_fname =
  let cout = open_out header_fname in
  P.fprintf cout "#ifndef _%s_GEN_H_INCLUDED_\n" compinfo.cname;
  P.fprintf cout "#define _%s_GEN_H_INCLUDED_\n\n" compinfo.cname;
  P.fprintf cout "#include <stdbool.h>\n";
  P.fprintf cout "#include \"lib/boilerplate_util.h\"\n\n";
  P.fprintf cout "#include \"%s\"\n\n" orig_fname;
  P.fprintf cout "%s\n\n" (gen_inductive_type compinfo);
  P.fprintf cout "%s\n\n" (gen_predicate compinfo);
  P.fprintf cout "%s\n\n" (gen_logical_hash compinfo);
  P.fprintf cout "%s\n\n" (gen_hash_decl compinfo);
  P.fprintf cout "%s\n\n" (gen_eq_function_decl compinfo);
  P.fprintf cout "%s\n\n" (gen_alloc_function_decl compinfo);
  P.fprintf cout "%s\n\n" (gen_log_fun_decl compinfo);
  P.fprintf cout "#ifdef KLEE_VERIFICATION\n";
  P.fprintf cout "#  include <klee/klee.h>\n";
  P.fprintf cout "#  include \"lib/stubs/containers/str-descr.h\"\n\n";
  P.fprintf cout "%s\n" (gen_str_field_descrs_decl compinfo);
  P.fprintf cout "#endif//KLEE_VERIFICATION\n\n";
  P.fprintf cout "#endif//_%s_GEN_H_INCLUDED_\n" compinfo.cname;
  close_out cout;
  ()

let traverse_globals (f : file) : unit =
  List.iter (fun g ->
    match g with
    | GCompTag (ifo, _) ->
      let header_fname = f.fileName ^ ".gen.h" in
      let impl_fname = f.fileName ^ ".gen.c" in
      fill_header_file ifo header_fname f.fileName;
      fill_impl_file ifo impl_fname header_fname;
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
  let usageMsg = "Usage: ciltutcc [options] source-files" in
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
