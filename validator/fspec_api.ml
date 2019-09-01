open Core
open Ir

(* FIXME: borrowed from ../codegen/data_spec.ml *)
type container = Map of string * string * string
               | Vector of string * string * string
               | CHT of string * string
               | DChain of string
               | Int
               | UInt
               | UInt32
               | EMap of string * string * string * string
               | LPM of string


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

let rec self_dereference tterm tmpgen =
  match tterm.v with
  | Id x -> begin match tterm.t with
      | Ptr _ ->
         ("//@ assert *&" ^ x ^ "|-> ?" ^
         (tmpgen ("pp" ^ x) ^ ";"),
         {v=Id (tmpgen ("pp" ^ x));t=tterm.t})
      | _ -> ("", tterm)
      end
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

let generate_2step_dereference tterm tmpgen =
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
    | _ -> failwith ("unhandled in inn_deref: " ^ (render_tterm tterm) ^
                     " : " ^ (ttype_to_str tterm.t))
  in

  let rec tterm_has_no_derefs = function
  | {v=Deref _;t=_} -> false
  | {v=Str_idx (x, _);t=_} -> tterm_has_no_derefs x
  | {v=Addr x;t=_} -> tterm_has_no_derefs x
  | _ -> true
  in
  match tterm.v with
  | Str_idx ({v=Deref {v=Id x;t=xt};t=dt}, fname) ->
    (* don't 2step-deref if there is only 1 step *)
    let binding = "//@ assert *&" ^ x ^ "|-> ?" ^ (tmpgen ("pp" ^ x)) ^ ";" in
    ([binding],{v=Str_idx ({v=Deref {v=Id (tmpgen ("pp" ^ x));t=xt};t=dt},
                           fname);
                t=tterm.t})
  | Str_idx ({v=Str_idx ({v=Deref {v=Id x; t=xt};t=ft1}, fname1);t=ft2},
             fname2) ->
    (*Keep the last deref*)
    let binding = "//@ assert *&" ^ x ^ "|-> ?" ^ (tmpgen ("pp" ^ x)) ^ ";" in
    ([binding],{v=Str_idx ({v=Str_idx ({v=Deref {v=Id (tmpgen ("pp" ^ x));
                                                 t=xt};t=ft1},
                                       fname1);
                            t=ft2}, fname2);
                t=tterm.t})
  | _ when tterm_has_no_derefs tterm ->
    (* don't do anything, can't use points-to if no derefs *)
    ([], tterm)
  | _ ->
    let (binding1,x) = self_dereference tterm tmpgen in
    let (binding2,x) = innermost_dereference x tmpgen in
    ([binding1;binding2],x)


type type_set = Static of ttype | Dynamic of (string*ttype) list

let stt types =
  List.map types ~f:(fun t -> Static t)

type fun_spec = {ret_type: type_set; arg_types: type_set list;
                 extra_ptr_types: (string * type_set) list;
                 lemmas_before: blemma list; lemmas_after: lemma list;}

let vigor_time_t = Sint64

module type Spec =
sig
  val records: ttype String.Map.t
  val containers: (string * container) list
end

let spec : (module Spec) option ref = ref None
