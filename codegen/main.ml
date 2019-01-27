open Cil
module F = Frontc
module E = Errormsg



let tut1FixInstr (i : instr) : bool =
  match i with
  | Set((Var vi, NoOffset), _, loc)
      when vi.vname = "deleted" && vi.vglob ->
    E.log "%a: Deleted assignment: %a\n" d_loc loc d_instr i;
    false
  | _ -> true


let rec tut1FixStmt (s : stmt) : unit =
  match s.skind with
  | Instr il ->
    s.skind <- Instr(List.filter tut1FixInstr il)
  | If(_,tb,fb,_) ->
    tut1FixBlock tb;
    tut1FixBlock fb
  

  | Switch(_,b,_,_) ->
    tut1FixBlock b
  | Loop(b,_,_,_) ->
    tut1FixBlock b
  | Block b ->
    tut1FixBlock b
  | TryFinally(b1, b2, _) ->
    tut1FixBlock b1;
    tut1FixBlock b2
  | TryExcept(b1,_,b2,_) ->
    tut1FixBlock b1;
    tut1FixBlock b2

  | _ -> ()

and tut1FixBlock (b : block) : unit = List.iter tut1FixStmt b.bstmts

let tut1FixFunction (fd : fundec) : unit = tut1FixBlock fd.sbody


let tut1 (f : file) : unit =
  List.iter (fun g ->
    match g with
    | GFun (fd, loc) when fd.svar.vname = "target" ->
      E.log "Processing our fun\n";
      tut1FixFunction fd
    | GCompTag (ifo, _) ->
      E.log "Found struct: %s\n" ifo.cname;
      E.log "bool %s_eq(void* a, void*b)\n\
              {\n  struct %s* id1 = a;\n  struct %s* id2 = b;\n  return " ifo.cname ifo.cname ifo.cname ;
      E.log "%s"
        (String.concat "\n     AND " (List.map (fun {fname;_} ->
             "id1->" ^ fname ^ " == id2->" ^ fname) ifo.cfields));
      E.log ";\n}\n";
      ()
    | GCompTagDecl (ifo, _) ->
      E.log "Found struct decl: %s\n" ifo.cname;
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
    E.log "starting\n";
    main () 
  with
  | F.CabsOnly -> ()
  | E.Error -> ()
end;
exit (if !E.hadErrors then 1 else 0)
