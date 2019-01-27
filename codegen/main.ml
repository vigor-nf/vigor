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

let gen_inductive_type compinfo =
  "/*@\ninductive " ^ (inductive_name compinfo) ^
  " = " ^ (constructor_name compinfo) ^ "(" ^
  (String.concat ", " (List.map (fun {ftype;_} ->
       P.sprint ~width:100 (d_type () ftype)
     ) compinfo.cfields)) ^
  "); @*/"

let gen_predicate compinfo =
  "/*@\npredicate " ^ (predicate_name compinfo) ^ "(struct " ^
  compinfo.cname ^ "* ptr; " ^ compinfo.cname ^ " v) = \n" ^
  "  struct_" ^ compinfo.cname ^ "_padding(ptr) &*&\n" ^
  (String.concat " &*&\n" (List.map (fun {fname;_} ->
       "  ptr->" ^ fname ^ " |-> ?" ^ fname ^ "_f"
     ) compinfo.cfields)) ^
   " &*&\n  v == " ^ (inductive_name compinfo) ^ "(" ^
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
    | hd::tl -> gen_exp_r tl ("(" ^ acc ^ " * 31 + " ^ hd.fname ^ ")")
    | [] -> acc
  in
  let gen_exp fields =
    match fields with
    | hd::tl -> gen_exp_r tl hd.fname
    | [] -> "(0)"
  in
  "/*@\nfixpoint unsigned " ^ (lhash_name compinfo) ^ "(" ^
  (inductive_name compinfo) ^ ") {\n  switch(" ^
  ") { case " ^ (constructor_name compinfo) ^ "(" ^
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

let traverse_globals (f : file) : unit =
  List.iter (fun g ->
    match g with
    | GCompTag (ifo, _) ->
      E.log "%s\n" (gen_inductive_type ifo);
      E.log "%s\n" (gen_predicate ifo);
      E.log "%s\n" (gen_logical_hash ifo);
      E.log "%s\n" (gen_hash_decl ifo);
      E.log "%s\n" (gen_hash ifo);
      E.log "%s\n" (gen_eq_function_decl ifo);
      E.log "%s\n" (gen_eq_function ifo);
      E.log "%s\n" (gen_alloc_function_decl ifo);
      E.log "%s\n" (gen_alloc_function ifo);
      E.log "%s\n" (gen_str_field_descrs_decl ifo);
      E.log "%s\n" (gen_str_field_descrs ifo);
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
