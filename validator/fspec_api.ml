open Core
open Ir

type lemma_params = {ret_name: string; ret_val: string;
                     args: string list;
                     arg_exps: tterm list;
                     tmp_gen: string -> string;
                     is_tip: bool; arg_types: ttype list;
                     exptr_types: ttype String.Map.t;
                     ret_type: ttype}

type blemma_params = {args: string list;
                      arg_exps: tterm list;
                      tmp_gen: string -> string;
                      is_tip: bool; arg_types: ttype list;
                      exptr_types: ttype String.Map.t;
                      ret_type: ttype}

type lemma = (lemma_params -> string)
type blemma = (blemma_params -> string)

let tx_l str = (fun _ -> "/*@ " ^ str ^ " @*/" )
let tx_bl str = (fun _ -> "/*@ " ^ str ^ " @*/" )


let on_rez_nonzero str = (fun params ->
    "/*@ if(" ^ params.ret_name ^ "!=0) " ^ str ^ "@*/")

let on_rez_nz f = (fun params ->
    "/*@ if(" ^ params.ret_name ^ "!=0) " ^ (f params) ^ " @*/")

let rec render_deep_assignment {lhs;rhs} =
  match rhs.t with
  | Str (_,fields) ->
    String.concat ~sep: "\n"
      (List.map fields
         ~f:(fun (name,t) ->
             render_deep_assignment {lhs={v=Str_idx (lhs, name);t};
                                     rhs={v=Str_idx (rhs, name);t}}))
  | Unknown -> "";
  | Array (_, s) -> "umemcpy(" ^ (render_tterm lhs) ^ ", " ^ (render_tterm rhs) ^ ", " ^ (Int.to_string s) ^ ");"
  | _ -> (render_tterm lhs) ^ " = " ^
         (render_tterm rhs) ^ ";"

let deep_copy (var : var_spec) =
  (render_deep_assignment {lhs={v=Id var.name;t=var.value.t};
                             rhs=var.value}) ^
  "\n"

let rec self_dereference tterm tmpgen =
  match tterm.v with
  | Id x -> ("//@ assert *&" ^ x ^ "|-> ?" ^
             (tmpgen ("pp" ^ x) ^ ";"),
             {v=Id (tmpgen ("pp" ^ x));t=tterm.t})
  | Str_idx (x,fname) ->
    let (binding, x) = self_dereference x tmpgen in
    (binding,{v=Str_idx (x,fname);t=tterm.t})
  | Addr x ->
    let (binding, x) = self_dereference x tmpgen in
    (binding,{v=Addr x;t=tterm.t})
  | Deref x ->
    let (binding, x) = self_dereference x tmpgen in
    (binding,{v=Deref x;t=tterm.t})
  | _ -> failwith ("unhandled in self_deref: " ^ (render_tterm tterm))

let rec innermost_dereference tterm tmpgen =
  match tterm.v with
  | Str_idx ({v=Deref {v=Id x;t=_};t=_},fname) ->
    let tmpname = (tmpgen ("stp" ^ x ^ "_" ^ fname)) in
    ("//@ assert " ^ (render_tterm tterm) ^ " |-> ?" ^
     tmpname ^ ";",
     {v=Id tmpname;t=tterm.t})
  | Addr x ->
    let (binding, x) = innermost_dereference x tmpgen in
    (binding, {v=Addr x;t=tterm.t})
  | Deref x ->
    let (binding, x) = innermost_dereference x tmpgen in
    (binding, {v=Deref x;t=tterm.t})
  | Str_idx (x,fname) ->
    let (binding, x) = innermost_dereference x tmpgen in
    (binding, {v=Str_idx (x,fname);t=tterm.t})
  | _ -> failwith ("unhandled in inn_deref: " ^ (render_tterm tterm) ^ " : " ^ (ttype_to_str tterm.t))

let generate_2step_dereference tterm tmpgen =
  let rec tterm_has_no_derefs = function
  | {v=Deref _;t=_} -> false
  | {v=Str_idx (x, _);t=_} -> tterm_has_no_derefs x
  | {v=Addr x;t=_} -> tterm_has_no_derefs x
  | _ -> true
  in
  match tterm.v with
  | Str_idx ({v=Deref {v=Id x;t=xt};t=dt}, fname) -> (* don't 2step-deref if there is only 1 step *)
    let binding = "//@ assert *&" ^ x ^ "|-> ?" ^ (tmpgen ("pp" ^ x)) ^ ";" in
    ([binding],{v=Str_idx ({v=Deref {v=Id (tmpgen ("pp" ^ x));t=xt};t=dt}, fname);t=tterm.t})
  | _ when tterm_has_no_derefs tterm -> (* don't do anything, can't use points-to if no derefs *)
    ([], tterm)
  | _ ->
    let (binding1,x) = self_dereference tterm tmpgen in
    let (binding2,x) = innermost_dereference x tmpgen in
    ([binding1;binding2],x)


type type_set = Static of ttype | Dynamic of (string*ttype) list

let stt types =
  List.map types ~f:(fun t -> Static t)

let estt ex_ptrs =
  List.map ex_ptrs ~f:(fun (name,t) -> (name,Static t))

type fun_spec = {ret_type: type_set; arg_types: type_set list;
                 extra_ptr_types: (string * type_set) list;
                 lemmas_before: blemma list; lemmas_after: lemma list;}

module type Spec =
sig
  val preamble  : string
  val fun_types : fun_spec Core.String.Map.t
  val fixpoints : Ir.tterm Core.String.Map.t
  val boundary_fun : string
  val finishing_fun : string
  val eventproc_iteration_begin : string
  val eventproc_iteration_end : string
  val user_check_for_complete_iteration : string
end

let spec : (module Spec) option ref = ref None
