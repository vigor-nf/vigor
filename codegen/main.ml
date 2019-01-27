open Cil
module F = Frontc
module E = Errormsg
module P = Pretty

let gen_inductive_type compinfo =
  "/*@ inductive " ^ compinfo.cname ^ "i = " ^ compinfo.cname ^ "c(" ^
  (String.concat ", " (List.map (fun {ftype;_} ->
       P.sprint ~width:100 (d_type () ftype)
     ) compinfo.cfields)) ^
  "); @*/"

let gen_predicate compinfo =
  "/*@ predicate " ^ compinfo.cname ^ "p(struct " ^
  compinfo.cname ^ "* ptr; " ^ compinfo.cname ^ " v) = \n" ^
  "  struct_" ^ compinfo.cname ^ "_padding(ptr) &*&\n" ^
  (String.concat " &*&\n" (List.map (fun {fname;_} ->
       "  ptr->" ^ fname ^ "|-> ?" ^ fname ^ "_field"
     ) compinfo.cfields)) ^
   " &*&\n  v == " ^ compinfo.cname ^ "i(" ^
  (String.concat ", " (List.map (fun {fname;_} ->
       fname ^ "_field"
     ) compinfo.cfields)) ^
  "); @*/"

let gen_eq_function compinfo =
  "bool " ^ compinfo.cname ^
  "_eq(void* a, void*b)\n\
   {\n  struct " ^ compinfo.cname ^
  "* id1 = a;\n  struct " ^ compinfo.cname ^
  "* id2 = b;\n  return " ^
  (String.concat "\n     AND " (List.map (fun {fname;_} ->
       "     id1->" ^ fname ^ " == id2->" ^ fname) compinfo.cfields)) ^
  ";\n}\n"


let tut1 (f : file) : unit =
  List.iter (fun g ->
    match g with
    | GCompTag (ifo, _) ->
      E.log "%s\n" (gen_inductive_type ifo);
      E.log "%s\n" (gen_predicate ifo);
      E.log "%s\n" (gen_eq_function ifo);
      ()
    | _ -> ())
  f.globals


let parseOneFile (fname: string) : file =
  E.log "parsing %s\n" fname;
  let cabs, cil = F.parse_with_cabs fname () in
  (* Rmtmps.removeUnusedTemps cil; *)
  cil

let processOneFile (cil: file) : unit =
  tut1 cil;
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
