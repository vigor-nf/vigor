open Cil
open Pretty

module E = Errormsg


type functions = {
    mutable turn_on : varinfo;
    mutable turn_off : varinfo;
    mutable track_conds : varinfo;
}

let dummyVar = makeVarinfo false "foo" voidType

let ciltut_funcs = {
    turn_on = dummyVar;
    turn_off = dummyVar;
    track_conds = dummyVar;
}

let initCilTutFunctions (f : file) : unit =
    let vvtype = TFun(voidType, Some [],false,[]) in
    ciltut_funcs.turn_on <- findOrCreateFunc f "__ciltut_turn_on" vvtype;
    ciltut_funcs.turn_off <- findOrCreateFunc f "__ciltut_turn_off" vvtype;

    let vuitype = TFun(voidType, Some["cond",uintType,[]], false, []) in
    ciltut_funcs.track_conds <- findOrCreateFunc f "__ciltut_track_conds" vuitype
;;

let v2e (vi : varinfo) : exp = Lval(Var vi, NoOffset)

let mk_turn_on_call (loc : location) : instr =
    Call(None, v2e ciltut_funcs.turn_on, [], loc)
let mk_turn_off_call (loc : location) : instr =
    Call(None, v2e ciltut_funcs.turn_off, [], loc)
let mk_track_cond_call (e : exp) (loc : location) : instr =
    Call(None, v2e ciltut_funcs.track_conds, [e], loc)

class condTrackInstrumenterClass = object(self)
    inherit nopCilVisitor

    method vstmt (s : stmt) =
        match s.skind with
        | If(e,_,_,loc) ->
            self#queueInstr [mk_track_cond_call e loc];
            DoChildren
        | _ -> DoChildren

    method vblock (b : block) =
        if not(hasAttribute "trackconds" b.battrs) then DoChildren else begin
        let turn_on_stmt = mkStmt (Instr[mk_turn_on_call (!currentLoc)]) in
        let turn_off_stmt = mkStmt (Instr[mk_turn_off_call (!currentLoc)]) in
        b.bstmts <- turn_on_stmt :: (b.bstmts @ [turn_off_stmt]);
        DoChildren
        end

end

let postProcess (f : file) : unit =
    f.globals <- (GText ("#include <ciltut.h>\n\n")) :: f.globals

let run (f : file) : unit =
    initCilTutFunctions f;
    visitCilFile (new condTrackInstrumenterClass) f;
    postProcess f
;;
