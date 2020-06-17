open Core
open Str
open Fspec_api
open Ir


let map_struct = Ir.Str ("Map", [])
let vector_struct = Ir.Str ("Vector", [] )
let dchain_struct = Ir.Str ("DoubleChain", [] )
let lpm_struct = Ir.Str ("lpm", [])

let rte_ether_addr_struct = Ir.Str ( "rte_ether_addr", ["addr_bytes", Array Uint8;])
let rte_ether_hdr_struct = Ir.Str ("rte_ether_hdr", ["d_addr", rte_ether_addr_struct;
                                             "s_addr", rte_ether_addr_struct;
                                             "ether_type", Uint16;])
let rte_ipv4_hdr_struct = Ir.Str ("rte_ipv4_hdr", ["version_ihl", Uint8;
                                           "type_of_service", Uint8;
                                           "total_length", Uint16;
                                           "packet_id", Uint16;
                                           "fragment_offset", Uint16;
                                           "time_to_live", Uint8;
                                           "next_proto_id", Uint8;
                                            "hdr_checksum", Uint16;
                                           "src_addr", Uint32;
                                           "dst_addr", Uint32;])
let tcpudp_hdr_struct = Ir.Str ("tcpudp_hdr", ["src_port", Uint16;
                                               "dst_port", Uint16])

let noop _ = ""

let c_type typ =
  if typ = "uint32_t" then typ else "struct " ^ typ

let ityp_name typ = if typ = "uint32_t" then "uint32_t" else typ ^ "i"
let hash_name name = name ^ "_hash"
let lhash_name name = "_" ^ name ^ "_hash"
let pred_name name = if name = "uint32_t" then "u_integer" else name ^ "p"
let alloc_fun_name typ =
  if typ = "uint32_t" then "null_init" else typ ^ "_allocate"
let eq_fun_name typ = typ ^ "_eq"
let lsim_variable_name typ = "last_" ^ typ ^ "_searched_in_the_map"
let lma_literal_name typ = "LMA_" ^ (StringLabels.uppercase_ascii typ)
let logic_name inv = inv ^ "l"
let advance_time_lemma inv = "advance_time_" ^ inv
let init_inv_lemma inv = "init_" ^ inv
let default_value_for typ = "DEFAULT_" ^ (String.uppercase typ)


let capture_a_map t name {tmp_gen;_} =
  "//@ assert mapp<" ^ ityp_name t ^ ">(_, _, _, _, mapc(_,?" ^
  (tmp_gen name) ^ ", _));\n"

let capture_chain ch_name ptr_num {args;tmp_gen;_} =
  "//@ assert double_chainp(?" ^ (tmp_gen ch_name) ^ ", " ^
  (List.nth_exn args ptr_num) ^ ");\n"

let common_fun_types =
  ["current_time", {ret_type = Static vigor_time_t;
                    arg_types = [];
                    extra_ptr_types = [];
                    lemmas_before = [];
                    lemmas_after = [
                      (fun params ->
                         "vigor_time_t now = " ^ (params.ret_name) ^ ";\n")];};
   "start_time", {ret_type = Static vigor_time_t;
                  arg_types = [];
                  extra_ptr_types = [];
                  lemmas_before = [];
                  lemmas_after = [];};
   "packet_receive", {ret_type = Static Boolean;
                      arg_types = stt [Uint16; Ptr (Ptr Sint8); Ptr Uint32];
                      extra_ptr_types = [];
                      lemmas_before = [];
                      lemmas_after = [
                        (fun {args;ret_name;_} ->
                           "a_packet_received = " ^ ret_name ^ " ;\n" ^
                           "received_on_port = " ^ (List.nth_exn args 0) ^ ";\n"
                        )
                      ];};
   "packet_send", {ret_type = Static Void;
                   arg_types = stt [Ptr Sint8; Uint16];
                   extra_ptr_types = [];
                   lemmas_before = [(fun {arg_exps;tmp_gen;_} ->
                       let packet_ptr =
                         (render_tterm (List.nth_exn arg_exps 0))
                       in
                       "char* " ^ (tmp_gen "synonym") ^ " = " ^ packet_ptr ^
                       ";\n/*@ {\n\ assert packetp(" ^ (tmp_gen "synonym") ^
                       ", ?cur_sent_packet, nil);\n\
                        if (last_sent_packet == nil) { \n\
                        assert packet_is_complete;\n\
                        switch(last_composed_packet) {\n\
                        case none: assert false;\n\
                        case some(cp): assert packetp(cp, cur_sent_packet, nil);\n\
                        }\n\
                        last_sent_packet = cur_sent_packet;\n\
                        } else {\n\
                        assert last_sent_packet == cur_sent_packet;\n\
                        }\n }\n @*/"
                     )];
                   lemmas_after = [(fun {args;_} ->
                       "sent_on_ports = cons((uint16_t)" ^ (List.nth_exn args 1) ^
                       ", sent_on_ports);\n"
                     )];};
   "packet_borrow_next_chunk", {ret_type = Static Void;
                                arg_types = [Static (Ptr Sint8);
                                             Static Uint32;
                                             Dynamic ["rte_ether_hdr",
                                                      Ptr (Ptr rte_ether_hdr_struct);
                                                      "rte_ipv4_hdr",
                                                      Ptr (Ptr rte_ipv4_hdr_struct);
                                                      "tcpudp_hdr",
                                                      Ptr (Ptr tcpudp_hdr_struct);
                                                      "ipv4_options",
                                                      Ptr (Ptr Sint8)
                                                     ]];
                                extra_ptr_types =
                                  ["the_chunk",
                                   Dynamic ["rte_ether_hdr",
                                            Ptr rte_ether_hdr_struct;
                                            "rte_ipv4_hdr",
                                            Ptr rte_ipv4_hdr_struct;
                                            "tcpudp_hdr",
                                            Ptr tcpudp_hdr_struct;
                                            "ipv4_options",
                                            Ptr Sint8
                                           ]];
                                lemmas_before =
                                  [(fun _ -> "//@ packet_is_complete = false;")];
                                lemmas_after = [
                                  (fun {args;arg_types;_} ->
                                     match (List.nth_exn arg_types 2) with
                                     | Ptr (Ptr (Str (_,_))) ->
                                       "//@ close_struct(*" ^
                                       (List.nth_exn args 2) ^ ");\n"
                                     | _ -> ""
                                  );
                                  (fun {args;arg_types;_} ->
                                     match List.nth_exn arg_types 2 with
                                     | Ptr (Ptr (Str ("rte_ether_hdr", _))) ->
                                       "//@ recv_headers = \
                                        add_rte_ether_header(recv_headers, *" ^
                                       (List.nth_exn args 2) ^ ");\n" ^
                                       "//@ open rte_ether_hdrp(*" ^
                                       (List.nth_exn args 2) ^
                                       ", _);\n\
                                        //@ open rte_ether_addrp((" ^
                                       (List.nth_exn args 2) ^
                                       "->s_addr), _);\n\
                                        //@ open rte_ether_addrp((" ^
                                       (List.nth_exn args 2) ^
                                       "->d_addr), _);\n"
                                     | Ptr (Ptr (Str ("rte_ipv4_hdr", _))) ->
                                       "//@ recv_headers = \
                                        add_rte_ipv4_header(recv_headers, *" ^
                                       (List.nth_exn args 2) ^ ");\n"
                                     | Ptr (Ptr (Str ("tcpudp_hdr", _))) ->
                                       "//@ recv_headers = \
                                        add_tcpudp_header(recv_headers, *" ^
                                       (List.nth_exn args 2) ^ ");\n"
                                     | Ptr (Ptr Sint8) ->
                                       ""
                                     | _ -> failwith
                                              "unsupported chunk type \
                                               in packet_borrow_next_chunk"
                                  )];};
   "packet_return_chunk", {ret_type = Static Void;
                           arg_types = [Static (Ptr Sint8);
                                        Dynamic ["rte_ether_hdr",
                                                 Ptr rte_ether_hdr_struct;
                                                 "rte_ipv4_hdr",
                                                 Ptr rte_ipv4_hdr_struct;
                                                 "tcpudp_hdr",
                                                 Ptr tcpudp_hdr_struct;
                                                 "ipv4_options",
                                                 Ptr Sint8
                                                ]];
                           extra_ptr_types = [];
                           lemmas_before = [
                             (fun {arg_exps;arg_types;_} ->
                                match List.nth_exn arg_types 1 with
                                | Ptr (Str ("rte_ether_hdr", _)) ->
                                  "//@ sent_headers = \
                                   add_rte_ether_header(sent_headers, " ^
                                  (render_tterm (List.nth_exn arg_exps 1)) ^
                                  ");\n\
                                   //@ open rte_ether_hdrp(" ^
                                  (render_tterm (List.nth_exn arg_exps 1)) ^
                                  ", _);\n\
                                   //@ open rte_ether_addrp(&(" ^
                                  (render_tterm (List.nth_exn arg_exps 1)) ^
                                  "->s_addr), _);\n\
                                   //@ open rte_ether_addrp(&(" ^
                                  (render_tterm (List.nth_exn arg_exps 1)) ^
                                  "->d_addr), _);\n"
                                | Ptr (Str ("rte_ipv4_hdr", _)) ->
                                  "//@ sent_headers = \
                                   add_rte_ipv4_header(sent_headers, " ^
                                  (render_tterm (List.nth_exn arg_exps 1)) ^
                                  ");\n"
                                | Ptr (Str ("tcpudp_hdr", _)) ->
                                  "//@ sent_headers = \
                                   add_tcpudp_header(sent_headers, " ^
                                  (render_tterm (List.nth_exn arg_exps 1)) ^
                                  ");\n"
                                | Ptr Sint8 ->
                                  ""
                                | _ -> failwith
                                         "unsupported chunk type \
                                          in packet_return_chunk"
                             );
                             (fun {arg_exps;arg_types;_} ->
                                match (List.nth_exn arg_types 1) with
                                | Ptr (Str (_, _)) ->
                                  "//@ open_struct(" ^
                                  (render_tterm (List.nth_exn arg_exps 1))
                                  ^ ");\n"
                                | _ -> ""
                             )];
                           lemmas_after = [(fun {arg_exps;tmp_gen;_} ->
                               let packet_ptr =
                                 (render_tterm (List.nth_exn arg_exps 0))
                               in
                               "char* " ^ (tmp_gen "synonym") ^ " = " ^
                               packet_ptr ^
                               ";\n/*@ {\n assert packetp(" ^
                               (tmp_gen "synonym") ^
                               ", _, ?unreturned_chunks);\n\
                                switch(last_composed_packet) {\n\
                                case none:\n\
                                last_composed_packet = some(" ^ packet_ptr ^
                               ");\n\
                                case some(cp):\n\
                                assert cp == " ^ packet_ptr ^
                               ";\n};\n\
                                packet_is_complete = \
                                (unreturned_chunks == nil);\n \
                                }\n@*/"
                             )];};
   "packet_get_unread_length", {ret_type = Static Uint32;
                                arg_types = stt [Ptr Sint8];
                                extra_ptr_types = [];
                                lemmas_before = [];
                                lemmas_after = [];};
   "packet_state_total_length", {ret_type = Static Void;
                                 arg_types = stt [Ptr Sint8;
                                                  Ptr Uint32];
                                 extra_ptr_types = [];
                                 lemmas_before = [(fun {args;} ->
                                     "packet_size = *" ^
                                     (List.nth_exn args 1) ^ ";\n")];
                                 lemmas_after = [];};
   "packet_free", {ret_type = Static Void;
                   arg_types = stt [Ptr Sint8;];
                   extra_ptr_types = [];
                   lemmas_before = [];
                   lemmas_after = [];};
   "lpm_allocate", {ret_type = Static Sint32;
                    arg_types = stt [Ptr (Ptr lpm_struct)];
                    extra_ptr_types = [];
                    lemmas_before = [];
                    lemmas_after = [];};
   "lpm_update_elem", {ret_type = Static Sint32;
                       arg_types = stt [Ptr lpm_struct;
                                        (* it is actually ui32, ui8, ui16*)
                                        Uint32; Uint16; Uint16];
                       extra_ptr_types = [];
                       lemmas_before = [];
                       lemmas_after = [];};
   "lpm_lookup_elem", {ret_type = Static Sint32;
                       arg_types = stt [Ptr lpm_struct; Uint32];
                       extra_ptr_types = [];
                       lemmas_before = [];
                       lemmas_after = [];};
  ]

type map_spec = {
  typ : string;
  coherent : bool;
  entry_type : ttype;
  invariant : string option;
}


let map_alloc_spec map_specs =
  {ret_type = Static Sint32;
   arg_types = stt [Fptr "map_keys_equality";
                    Fptr "map_key_hash";
                    Uint32;
                    Ptr (Ptr map_struct)];
   extra_ptr_types = [];
   lemmas_before = [
     (fun _ -> "/*@\n\
        switch(map_allocation_order) {\n" ^
        (String.concat ~sep:"" (List.mapi map_specs ~f:(fun i {typ;_} ->
             " case " ^ (string_of_int i) ^
             ":\n\
              produce_function_pointer_chunk \
              map_keys_equality<" ^ ityp_name typ ^ ">(" ^ eq_fun_name typ ^
             ")\
              (" ^ pred_name typ ^
             ")(a, b) \
              {\
              call();\
              }\n\
              produce_function_pointer_chunk \
              map_key_hash<" ^ ityp_name typ ^ ">(" ^ hash_name typ ^
             ")\
              (" ^ pred_name typ ^ ", " ^ lhash_name typ ^
             ")(a) \
              {\
              call();\
              }\n\
              break;\n"
           )) ) ^
          "default:\n\
            assert false;\n\
        }\n@*/") ;
   ];
   lemmas_after = [
     (fun {tmp_gen;_} ->
        "/*@ \n\
        switch(map_allocation_order) {\n" ^
        (String.concat ~sep:"" (List.mapi map_specs ~f:(fun i {typ;_} ->
             let pred = pred_name typ in
             " case " ^ (string_of_int i) ^
             ":\n\
              assert [?" ^ (tmp_gen "imkest") ^
             "]is_map_keys_equality(" ^ eq_fun_name typ ^ ",\
              " ^ pred ^ ");\n\
              close [" ^ (tmp_gen "imkest") ^
             "]hide_is_map_keys_equality(" ^ eq_fun_name typ ^ ", \
              " ^ pred ^ ");\n\
              assert [?" ^ (tmp_gen "imkhst") ^
             "]is_map_key_hash(" ^ hash_name typ ^ ",\
              " ^ pred ^ ", " ^ lhash_name typ ^ ");\n\
              close [" ^ (tmp_gen "imkhst") ^
             "]hide_is_map_key_hash(" ^ hash_name typ ^ ", \
              " ^ pred ^ ", " ^ lhash_name typ ^ ");\n\
              break;\n"
           )) ) ^
          "default:\n\
            assert false;\n\
        }\n @*/");
     (fun _ ->
        "map_allocation_order += 1;");];}

type vector_params = {
  name : string;
  typ : string;
  has_keeper : bool;
  entry_type : ttype;
  invariant : string option;
}

let vector_alloc_spec vector_specs =
  {ret_type = Static Sint32;
   arg_types = stt [Sint32;
                    Uint32;
                    Fptr "vector_init_elem";
                    Ptr (Ptr vector_struct)];
   extra_ptr_types = [];
   lemmas_before = [
     (fun _ -> "/*@\n\
        switch(vector_allocation_order) {\n" ^
        (String.concat ~sep:"" (List.mapi vector_specs ~f:(fun i {typ;_} ->
             " case " ^ (string_of_int i) ^ ":\n\
              produce_function_pointer_chunk \
              vector_init_elem<" ^ ityp_name typ ^ ">(" ^ alloc_fun_name typ ^
             ")(" ^ (pred_name typ) ^
             ", sizeof(" ^ (c_type typ) ^
             "), " ^ default_value_for typ ^
             ")(a) \
              {\
              call();\
              }\n\
              break;\n"
           )) ) ^
          "default:\n\
            assert false;\n\
        }\n@*/");
     (fun {args;_} ->
       ("\n\
        switch(vector_allocation_order) {\n" ^
        (String.concat ~sep:"" (List.mapi vector_specs ~f:(fun i {name;typ;invariant;_} ->
             " case " ^ (string_of_int i) ^ ":\n\
               //@assume(sizeof(" ^ (c_type typ) ^ ") == " ^
             (List.nth_exn args 0) ^
             ");\n" ^
             (match invariant with
              | Some inv ->
                "//@ " ^ (init_inv_lemma inv) ^
                "(nat_of_int(" ^
                (List.nth_exn args 1) ^
                "), recent_time_" ^ name ^ ");\n"
              | None -> ""
             ) ^
             "break;\n"
           )) ) ^
          "default:\n\
            assert false;\n\
        }\n"));
   ];
   lemmas_after = [
     (fun {tmp_gen;ret_name;_} ->
       ("\n\
        switch(vector_allocation_order) {\n" ^
        (String.concat ~sep:"" (List.mapi vector_specs
                                  ~f:(fun i {typ;has_keeper;invariant;_} ->
             " case " ^ (string_of_int i) ^ ":\n" ^
             (if has_keeper then
                "/*@ if (" ^ ret_name ^
                ") {\n\
                 assert mapp<" ^ ityp_name typ ^ ">(_, _, _, _, mapc(?" ^
                (tmp_gen "cap") ^
                ", ?" ^ (tmp_gen "map") ^
                ", ?" ^ (tmp_gen "addr_map") ^
                "));\n\
                 assert vectorp<" ^ ityp_name typ ^ ">(_, _, ?" ^
                (tmp_gen "dks") ^
                ", ?" ^ (tmp_gen "dkaddrs") ^
                ");\n\
                 empty_kkeeper(" ^
                (tmp_gen "dkaddrs") ^
                ", " ^ (tmp_gen "dks") ^
                ", " ^ (tmp_gen "addr_map") ^
                ", " ^ (tmp_gen "cap") ^
                ");\n" ^
                "}@*/"
              else
                "") ^
             "break;\n"
           )) ) ^
          "default:\n\
            assert false;\n\
           }\n"));
     (fun _ ->
        "vector_allocation_order += 1;")];}

let open_callback entry_type arg =
  match entry_type with
  | Str (name, fields) -> "//@ open [_]" ^ pred_name name ^
                          "(" ^ render_tterm arg ^ ", _);\n" ^
                          (String.concat ~sep:"" (List.map fields
                                                    ~f:(fun (name,ttype) ->
                               match ttype with
                               | Str (str_name, _) ->
                                 "//@ open [_]" ^ pred_name str_name ^ "(" ^
                                 render_tterm (simplify_tterm
                                                 {v=Addr
                                                      {v=Str_idx ({v=Deref arg;
                                                                   t=Unknown},
                                                                  name);
                                                       t=ttype};
                                                  t=Unknown}) ^ ", _);\n"
                               | _ -> "")))
  | Uint32 -> ""
  | _ -> "#error open callback is not implemented"

let vector_borrow_spec entry_specs =
  let other_types excl_typ =
    List.filter entry_specs ~f:(fun {typ;_} ->
        typ <> excl_typ)
  in
  {ret_type = Static Void;
   arg_types = [Static (Ptr vector_struct);
                Static Sint32;
                Dynamic (List.map entry_specs ~f:(fun {typ;entry_type;_} ->
                  (typ, Ptr (Ptr entry_type))));];
   extra_ptr_types = ["borrowed_cell",
                      Dynamic (List.map entry_specs ~f:(fun {typ;entry_type;_} ->
                        (typ, Ptr entry_type)));];
   lemmas_before = [
     (fun {arg_types;args;tmp_gen;_} ->
        match (List.find_map entry_specs ~f:(fun {typ;entry_type;has_keeper;_} ->
             if (List.nth_exn arg_types 2) = (Ptr (Ptr entry_type)) then
               let ityp = ityp_name typ in
               Some ((String.concat ~sep:""
                        (List.map (other_types typ)
                           ~f:(fun {typ;_} ->
                               "//@ close hide_vector<" ^
                               ityp_name typ ^ ">(_, _, _, _);\n"
                             ))) ^ "//@ assert vectorp<" ^ ityp ^ ">(" ^
                     (List.nth_exn args 0) ^
                     ", " ^ pred_name typ ^ ", ?" ^ (tmp_gen "vec") ^ ", ?" ^
                     (tmp_gen "veca") ^
                     ");\n//@ vector_addrs_same_len_nodups(" ^
                     (List.nth_exn args 0) ^ ");\n" ^
                     (if has_keeper then
                        "/*@ {\n\
                         assert mapp<" ^ ityp ^ ">(_, _, _, _, mapc(_,?" ^
                        (tmp_gen "fm") ^
                        ", ?" ^ (tmp_gen "fma") ^
                        "));\n\
                         forall2_nth(" ^ (tmp_gen "vec") ^ ", " ^
                        (tmp_gen "veca") ^
                        ", (kkeeper)(" ^ (tmp_gen "fma") ^ "), " ^
                        (List.nth_exn args 1) ^
                        ");\n} @*/ "
                      else
                        "//@ forall_mem(nth(" ^ (List.nth_exn args 1) ^
                        ", " ^ (tmp_gen "vec") ^ "), " ^ (tmp_gen "vec") ^
                        ", is_one);"))
             else
               None
           ))
        with
        | Some x -> x
        | None -> "Error: unexpected argument type: " ^
                  (ttype_to_str (List.nth_exn arg_types 2)));];
   lemmas_after = [
     (fun {arg_types;args;arg_exps;tmp_gen;_} ->
        match (List.find_map entry_specs ~f:(fun {typ;entry_type;invariant;name;_} ->
            if (List.nth_exn arg_types 2) = (Ptr (Ptr entry_type)) then
              Some (String.concat ~sep:""
                      (List.map (other_types typ) ~f:(fun {typ;_} ->
                           "//@ open hide_vector<" ^ ityp_name typ ^
                           ">(_, _, _, _);\n")) ^
                    begin match invariant with
                      | Some invariant ->
                        "//@ forall_nth(" ^ (tmp_gen "vec") ^
                        ", (sup)((" ^ (logic_name invariant) ^
                        ")(recent_time_" ^ name ^ "), fst), " ^
                        (List.nth_exn args 1) ^
                        ");\n" ^
                        let (binding,expr) =
                          self_dereference (List.nth_exn arg_exps 2) tmp_gen
                        in
                        let Addr expr = expr.v in
                        binding ^
                        "\n//@ assert [_]" ^ pred_name typ ^ "(" ^ (render_tterm expr) ^
                        ", ?" ^ (tmp_gen "fk") ^ ");\n" ^
                        "//@ forall_update(" ^ (tmp_gen "vec") ^
                        ", (sup)((" ^ (logic_name invariant) ^
                        ")(recent_time_" ^ name ^ "), fst), " ^
                        (List.nth_exn args 1) ^
                        ", pair(" ^ (tmp_gen "fk") ^
                        ", 0.0));\n"
                      | None -> ""
                    end ^
                    (open_callback entry_type
                       {v=Deref (List.nth_exn arg_exps 2);
                        t=Unknown}))
            else
              None))
        with
        | Some x -> x
        | None -> "Error: unexpected argument type: " ^
                  (ttype_to_str (List.nth_exn arg_types 2)))];}

let vector_return_spec entry_specs =
  let other_types excl_typ =
    List.filter entry_specs ~f:(fun {typ;_} ->
        typ <> excl_typ)
  in
  {ret_type = Static Void;
   arg_types = [Static (Ptr vector_struct);
                Static Sint32;
                Dynamic (List.map entry_specs ~f:(fun {typ;entry_type;_} ->
                    (typ, Ptr entry_type)));];
   extra_ptr_types = [];
   lemmas_before = [
     (fun {arg_types;args;arg_exps;tmp_gen;_} ->
        match (List.find_map entry_specs
                 ~f:(fun {name;typ;entry_type;invariant;_} ->
            if (List.nth_exn arg_types 2) = (Ptr entry_type) then
              Some (String.concat ~sep:""
                      (List.map (other_types typ)
                         ~f:(fun {typ;_} ->
                             "//@ close hide_vector<" ^ ityp_name typ ^
                             ">(_, _, _, _);\n"
                       )) ^
                    "\n" ^ "//@ assert vectorp<" ^ ityp_name typ ^
                    ">(" ^
                    (List.nth_exn args 0) ^
                    ", " ^ pred_name typ ^ ", ?" ^ (tmp_gen "vec") ^ ", ?" ^
                    (tmp_gen "veca") ^
                    ");\n" ^
                    begin match invariant with
                      | Some invariant ->
                        let (binding,expr) =
                          self_dereference (List.nth_exn arg_exps 2) tmp_gen
                        in
                        binding ^
                        "\n//@ assert [?" ^ (tmp_gen "frac") ^ "]" ^
                        pred_name typ ^ "(" ^ (render_tterm expr) ^
                        ", ?" ^ (tmp_gen "fk") ^ ");\n" ^
                        "//@ assert last_time(?" ^ tmp_gen "new_recent_time" ^ ");\n" ^
                        "//@ " ^ advance_time_lemma invariant ^
                        "(" ^ (tmp_gen "vec") ^
                        ", recent_time_" ^ name ^ ", " ^ tmp_gen "new_recent_time" ^");\n" ^
                        "recent_time_" ^ name ^ " = " ^ tmp_gen "new_recent_time" ^ ";\n" ^
                        "//@ forall_update(" ^ (tmp_gen "vec") ^
                        ", (sup)((" ^ (logic_name invariant) ^
                        ")(recent_time_" ^ name ^ "), fst), " ^
                        (List.nth_exn args 1) ^
                        ", pair(" ^ (tmp_gen "fk") ^
                        ", " ^ (tmp_gen "frac") ^ "));\n"
                      | None -> ""
                    end)
            else
              None))
        with
        | Some x -> x
        | None -> "Error: unexpected argument type: " ^
                  (ttype_to_str (List.nth_exn arg_types 2)))];
   lemmas_after = [
     (fun {arg_types;args;tmp_gen;_} ->
        match (List.find_map entry_specs ~f:(fun {typ;entry_type;_} ->
            if (List.nth_exn arg_types 2) = (Ptr entry_type) then
              Some (String.concat ~sep:""
                      (List.map (other_types typ)
                         ~f:(fun {typ;_} ->
                             "//@ open hide_vector<" ^ ityp_name typ ^ ">(_, _, _, _);\n"
                           )))
            else
              None))
        with
        | Some x -> x
        | None -> "Error: unexpected argument type: " ^
                  (ttype_to_str (List.nth_exn arg_types 2)))];}

let dchain_alloc_spec dchain_specs =
  {ret_type = Static Sint32;
   arg_types = stt [Sint32; Ptr (Ptr dchain_struct)];
   extra_ptr_types = [];
   lemmas_before = [];
   lemmas_after =
     [(fun {ret_name;args;_} ->
        "switch(dchain_allocation_order) {\n" ^
        (String.concat ~sep:"" (List.mapi dchain_specs ~f:(fun i typ ->
             " case " ^ (string_of_int i) ^ ":\n" ^
             "//@ index_range_of_empty(" ^ (List.nth_exn args 0) ^ ", 0);\n" ^
             "/*@ if (" ^ ret_name ^
             " != 0) {\n\
              assert vectorp<" ^ ityp_name typ ^
             ">(_, _, ?allocated_vector, _);\n\
              empty_map_vec_dchain_coherent\
              <" ^ ityp_name typ ^ ">(allocated_vector);\n} @*/\n" ^
             "break;\n"
           ))) ^
        "default:\n\
         assert false;\n\
         }\n" ^
     "dchain_allocation_order += 1;")]}

let loop_invariant_consume_spec_impl types =
  {ret_type = Static Void;
   arg_types = stt (List.map types ~f:(fun (_, _, t) -> t)) ;
   extra_ptr_types = [];
   lemmas_before = [
     (fun {arg_exps;tmp_gen;_} ->
        "//@ assert last_time(?last_recent_time);\n" ^
        (String.concat ~sep:""
           (List.map2_exn arg_exps types ~f:(fun arg (name, t, _) ->
                match t with
                | Vector (typ, _, inv) when inv <> "" ->
                  let (binding,expr) =
                    self_dereference arg tmp_gen
                  in
                  let Addr arg = expr.v in
                  binding ^ "\n" ^
                  "//@ assert vectorp<" ^ ityp_name typ ^ ">(" ^
                  (render_tterm arg) ^ ", " ^ pred_name typ ^ ", ?"
                  ^ (tmp_gen (typ ^ "vec")) ^
                  ", _);\n"^
                  "//@ " ^ advance_time_lemma inv ^ "(" ^ (tmp_gen (typ ^ "vec")) ^
                  ", recent_time_" ^ name ^ ", last_recent_time);\n" ^
                  "recent_time_" ^ name ^ " = last_recent_time;\n"
                | Map (typ, _, inv) when inv <> "" ->
                  let (binding,expr) =
                    self_dereference arg tmp_gen
                  in
                  let Addr arg = expr.v in
                  binding ^ "\n" ^
                  "//@ assert mapp<" ^ ityp_name typ ^ ">(" ^
                  (render_tterm arg) ^ ", " ^ pred_name typ ^
                  ", _, _, mapc(_, ?"
                  ^ (tmp_gen (typ ^ "map")) ^
                  ", _));\n"^
                  "//@ " ^ advance_time_lemma inv ^ "(" ^ (tmp_gen (typ ^ "map")) ^
                  ", initial_time, last_recent_time);\n"
                | _ -> ""
              ))));
     (fun {args;_} ->
        "/*@ close evproc_loop_invariant(" ^
        (String.concat ~sep:", "
           (List.map2_exn args types ~f:(fun arg (_, _, t) ->
                match t with
                | Ptr _ -> "*" ^ arg
                | _ -> arg
              )  )) ^ "); @*/");
   ];
   lemmas_after = [];}

let concrete_containers containers =
  List.filter containers ~f:(function
      | _, EMap (_, _, _, _) -> false
      | _ -> true)

let gen_vector_params containers records =
  let has_keeper vec = List.exists containers ~f:(fun (_,ctyp) ->
      match ctyp with
      | EMap (_, _, emap_vec, _) -> vec = emap_vec
      | _ -> false)
  in
  List.filter_map containers ~f:(fun (name,ctyp) ->
      match ctyp with
      | Vector (typ, _, invariant) -> Some {name;typ;has_keeper=has_keeper name;
                                            entry_type=String.Map.find_exn records typ;
                                            invariant=if invariant = "" then None
                                                  else Some invariant}
      | CHT (_, _) -> Some {name;typ="uint32_t";has_keeper=false;entry_type=Uint32;
                            invariant=None}
      | _ -> None)


let loop_invariant_arg_types containers =
  (List.map containers ~f:(fun (name,t) ->
       name, t,
       match t with
       | Map (_, _, _) -> (Ptr (Ptr map_struct))
       | Vector (_, _, _) -> (Ptr (Ptr vector_struct))
       | CHT (_, _) -> (Ptr (Ptr vector_struct))
       | DChain _ -> (Ptr (Ptr dchain_struct))
       | Int -> Sint32
       | UInt -> Uint32
       | UInt32 -> Uint32
       | EMap (_, _, _, _) -> Void
       | LPM _ -> (Ptr (Ptr lpm_struct))))@["lcore", UInt32, Uint32;
                                            "time", Int, vigor_time_t]

let loop_invariant_consume_spec containers records =
  loop_invariant_consume_spec_impl (loop_invariant_arg_types
                                      (concrete_containers containers))

let loop_invariant_produce_spec containers =
  let linv_prod_arg_types =
    ((List.map (concrete_containers containers) ~f:(fun (name,t) ->
         match t with
         | Map (_, _, _) -> (Ptr (Ptr map_struct))
         | Vector (_, _, _) -> (Ptr (Ptr vector_struct))
         | CHT (_, _) -> (Ptr (Ptr vector_struct))
         | DChain _ -> (Ptr (Ptr dchain_struct))
         | Int -> Sint32
         | UInt -> Uint32
         | UInt32 -> Uint32
         | EMap (_, _, _, _) -> Void
         | LPM _ -> (Ptr (Ptr lpm_struct))))@[Ptr Uint32; Ptr vigor_time_t])
  in
  {ret_type = Static Void;
   arg_types = stt linv_prod_arg_types;
   extra_ptr_types = [];
   lemmas_before = [];
   lemmas_after = [
     (fun {args;_} ->
        "/*@ open evproc_loop_invariant (" ^
        (String.concat ~sep:", " (List.mapi linv_prod_arg_types
                                    ~f:(fun i argt ->
                                        match argt with
                                        | Ptr _ -> "*" ^ (List.nth_exn args i)
                                        | _ -> (List.nth_exn args i)))) ^
        "); @*/\n");
     (fun {args;tmp_gen;_} ->
        "initial_time = *" ^ (List.last_exn args) ^ ";\n" ^
        "/*@ {\n" ^
        (String.concat ~sep:""
           (List.mapi (concrete_containers containers)
              ~f:(fun i (name,t) ->
                  match t with
                  | Map (typ, _, _) ->
                    "assert *" ^ (List.nth_exn args i) ^ " |-> ?" ^
                    (tmp_gen (name ^ "_tmp")) ^
                    ";\n assert mapp<" ^ (ityp_name typ) ^ ">(" ^
                    (tmp_gen (name ^ "_tmp")) ^ ", _, _, _, mapc(_, ?" ^
                    (tmp_gen ("initial_" ^ name)) ^ ", _));\n" ^
                    "initial_" ^ name ^ " = " ^
                    (tmp_gen ("initial_" ^ name)) ^ ";\n" ^ name ^ "_ptr = " ^
                    (tmp_gen (name ^ "_tmp")) ^ ";\n"
                  | Vector (typ, _, _) ->
                    "assert *" ^ (List.nth_exn args i) ^ " |-> ?" ^
                    (tmp_gen (name ^ "_tmp")) ^
                    ";\n assert vectorp<" ^ (ityp_name typ) ^ ">(" ^
                    (tmp_gen (name ^ "_tmp")) ^ ", _, ?" ^
                    (tmp_gen ("initial_" ^ name)) ^ ", _);\n" ^
                    "initial_" ^ name ^ " = " ^ (tmp_gen ("initial_" ^ name)) ^
                    ";\n" ^
                    name ^ "_ptr = " ^ (tmp_gen (name ^ "_tmp")) ^ ";\n" ^
                    "\n}@*/\nrecent_time_" ^ name ^ " = initial_time;\n/*@{\n"
                  | CHT (_, _) ->
                    "assert *" ^ (List.nth_exn args i) ^ " |-> ?" ^
                    (tmp_gen (name ^ "_tmp")) ^
                    ";\n assert vectorp<uint32_t>(" ^
                    (tmp_gen (name ^ "_tmp")) ^ ", _, ?" ^
                    (tmp_gen ("initial_" ^ name)) ^ ", _);\n" ^
                    "initial_" ^ name ^ " = " ^
                    (tmp_gen ("initial_" ^ name)) ^ ";\n" ^
                    name ^ "_ptr = " ^ (tmp_gen (name ^ "_tmp")) ^ ";\n"
                  | DChain _ ->
                    "assert *" ^ (List.nth_exn args i) ^ " |-> ?" ^
                    (tmp_gen (name ^ "_tmp")) ^
                    ";\n assert double_chainp(?" ^
                    (tmp_gen ("initial_" ^ name)) ^ ", " ^
                    (tmp_gen (name ^ "_tmp")) ^ ");\n" ^
                    "initial_" ^ name ^ " = " ^
                    (tmp_gen ("initial_" ^ name)) ^ ";\n" ^
                    name ^ "_ptr = " ^ (tmp_gen (name ^ "_tmp")) ^ ";\n"
                  | Int
                  | UInt
                  | UInt32 -> name ^ " = " ^ (List.nth_exn args i) ^ ";\n"
                  | EMap (_, _, _, _) -> "#error unexpected abstract container\n"
                  | LPM _ ->
                    "assert *" ^ (List.nth_exn args i) ^ " |-> ?" ^
                    (tmp_gen (name ^ "_tmp")) ^
                    ";\n assert table(" ^
                    (tmp_gen (name ^ "_tmp")) ^ ",?" ^
                    (tmp_gen ("initial_" ^ name)) ^ ");\n" ^
                    "initial_" ^ name ^ " = " ^
                    (tmp_gen ("initial_" ^ name)) ^ ";\n" ^
                    name ^ "_ptr = " ^
                    (tmp_gen (name ^ "_tmp")) ^ ";\n"
                ))) ^
        "\n}@*/\n");
   ];}

let constructor_name typ = typ ^ "c"

let construct_record var tt =
  match tt with
  | Ir.Str (name, fields) ->
    (constructor_name name) ^ "(" ^
    (String.concat ~sep:", "
       (List.map fields ~f:(fun (name,ft) ->
            match ft with
            | Array _ -> (* HACK: we know that the only arrays in use are the
                            rte_ether_addr ones that have exactly 6 cells. so we
                            hardcode it here. The right way to go about this is
                            to add another type StaticArray that would keep
                            track of the array size.*)
              var ^ "->" ^ name ^ "[0], " ^
              var ^ "->" ^ name ^ "[1], " ^
              var ^ "->" ^ name ^ "[2], " ^
              var ^ "->" ^ name ^ "[3], " ^
              var ^ "->" ^ name ^ "[4], " ^
              var ^ "->" ^ name ^ "[5]"
            | _ ->
              var ^ "->" ^ name))) ^ ")"
  | _ -> "#error construction of non-structs is not supported"

let hash_spec record_type =
  match record_type with
  | Ir.Str (name, _) ->
    (hash_name name , {ret_type = Static Uint32;
                       arg_types = stt [Ptr record_type];
                       extra_ptr_types = [];
                       lemmas_before = [];
                       lemmas_after = [
                         (fun {args;_} ->
                            "//@ open " ^ (pred_name name) ^
                            "(" ^ (List.nth_exn args 0) ^ ", _);\n")];})
  | _ -> failwith "Non struct record types are not supported"


let map_get_spec (map_specs : map_spec list) =
  let other_specs excl_typ =
    List.filter map_specs ~f:(fun {typ;_} ->
        typ <> excl_typ)
  in
  {ret_type = Static Sint32;
   arg_types = [Static (Ptr map_struct);
                Dynamic (List.map map_specs ~f:(fun {typ;entry_type;_} ->
                  typ, Ptr entry_type));
                Static (Ptr Sint32)];
   extra_ptr_types = [];
   lemmas_before = [
     (fun ({arg_exps;tmp_gen;arg_types;args;_} as params) ->
        match (List.find_map map_specs ~f:(fun {typ;entry_type;coherent;_} ->
            if (List.nth_exn arg_types 1) = (Ptr entry_type) then
              Some (
                (String.concat ~sep:""
                   (List.map (other_specs typ)
                      ~f:(fun {typ;_} ->
                          "//@ close hide_mapp<" ^ ityp_name typ ^
                          ">(_, _, _, _, _);\n"
                        ))) ^
                capture_a_map typ "map" params ^
                (if coherent then
                   let (binding,expr) =
                     self_dereference (List.nth_exn arg_exps 1) tmp_gen
                   in
                   binding ^
                   "\n//@ assert " ^ pred_name typ ^ "(" ^ (render_tterm expr) ^
                   ", ?" ^ (tmp_gen "fk") ^ ");\n" ^
                   lsim_variable_name typ ^ " = " ^ (tmp_gen "fk") ^ ";\n" ^
                   "//@ assert map_vec_chain_coherent<" ^ ityp_name typ ^ ">(" ^
                   (tmp_gen "map") ^ ", ?" ^
                   (tmp_gen "dv") ^ ", ?" ^
                   (tmp_gen "dh") ^ ");\n"
                 else ""))
            else
              None))
        with
        | Some x -> x
        | None -> "Error: unexpected argument type: " ^
                  (ttype_to_str (List.nth_exn arg_types 1))

     );];
   lemmas_after = [
     (fun {ret_name;tmp_gen;arg_types;args;arg_exps;_} ->
        match (List.find_map map_specs ~f:(fun {typ;entry_type;
                                                coherent;invariant} ->
            if (List.nth_exn arg_types 1) = (Ptr entry_type) then
              Some ((if coherent then
                       "/*@ if (" ^ ret_name ^
                       " != 0) {\n\
                        mvc_coherent_map_get_bounded(" ^
                       (tmp_gen "map") ^ ", " ^
                       (tmp_gen "dv") ^ ", " ^
                       (tmp_gen "dh") ^ ", " ^
                       (tmp_gen "fk") ^
                       ");\n\
                        mvc_coherent_map_get_vec_half(" ^
                       (tmp_gen "map") ^ ", " ^
                       (tmp_gen "dv") ^ ", " ^
                       (tmp_gen "dh") ^ ", " ^
                       (tmp_gen "fk") ^
                       ");\n\
                        mvc_coherent_map_get(" ^
                       (tmp_gen "map") ^ ", " ^
                       (tmp_gen "dv") ^ ", " ^
                       (tmp_gen "dh") ^ ", " ^
                       (tmp_gen "fk") ^ ");\n} @*/\n" ^
                       "last_map_accessed = " ^ lma_literal_name typ ^ ";\n"
                     else "") ^
                    (match invariant with
                     | Some invariant ->
                       "\n//@ assert " ^ pred_name typ ^
                       "(" ^ (List.nth_exn args 1) ^
                       ", ?" ^ (tmp_gen "fkk") ^ ");\n" ^
                       "/*@ if (" ^ ret_name ^
                       " != 0) {\n" ^
                       "\nmap_get_inv_holds(" ^
                       (tmp_gen "map") ^ ", " ^
                       (tmp_gen "fkk") ^ ", (" ^
                       (logic_name invariant) ^ ")(initial_time));
                     \n} @*/\n"
                     | None -> "")
                    ^
                    (open_callback entry_type (List.nth_exn arg_exps 1)) ^
                    (String.concat ~sep:"" (List.map (other_specs typ)
                                              ~f:(fun {typ;_} ->
                                                  "//@ open hide_mapp<" ^
                                                  ityp_name typ ^
                                                  ">(_, _, _, _, _);\n"
                                                )))
                   )
            else
              None))
        with
        | Some x -> x
        | None -> "Error: unexpected argument type: " ^
                  (ttype_to_str (List.nth_exn arg_types 1)));
   ];}

let map_put_spec (map_specs : map_spec list) =
  let other_specs excl_typ =
    List.filter map_specs ~f:(fun {typ;_} ->
        typ <> excl_typ)
  in
  {ret_type = Static Void;
   arg_types = [Static (Ptr map_struct);
                Dynamic (List.map map_specs ~f:(fun {typ;entry_type;_} ->
                  typ, Ptr entry_type));
                Static Sint32];
   extra_ptr_types = [];
   lemmas_before = [
     (fun {args;tmp_gen;arg_types;_} ->
        match (List.find_map map_specs ~f:(fun {typ;entry_type;coherent;_} ->
            if (List.nth_exn arg_types 1) = (Ptr entry_type) then
              Some (
                (String.concat ~sep:""
                   (List.map (other_specs typ)
                      ~f:(fun {typ;_} ->
                          "//@ close hide_mapp<" ^ ityp_name typ ^ ">(_, _, _, _, _);\n"
                        ))) ^
                if coherent then
                  let ityp = ityp_name typ in
                  "\n//@ assert mapp<" ^ ityp ^ ">(_, _, _, _, mapc(_, ?" ^
                  (tmp_gen "dm") ^
                  ", _));\n" ^
                  "\n/*@ {\n\
                   assert map_vec_chain_coherent<" ^ ityp ^ ">(" ^
                  (tmp_gen "dm") ^ ", ?" ^
                  (tmp_gen "dv") ^ ", ?" ^
                  (tmp_gen "dh") ^
                  ");\n\
                   mvc_coherent_dchain_non_out_of_space_map_nonfull<" ^ ityp ^
                  ">(" ^
                  (tmp_gen "dm") ^ ", " ^
                  (tmp_gen "dv") ^ ", " ^
                  (tmp_gen "dh") ^ ");\n" ^
                  "mvc_coherent_bounds<" ^ ityp ^ ">(" ^
                  (tmp_gen "dm") ^ ", " ^
                  (tmp_gen "dv") ^ ", " ^
                  (tmp_gen "dh") ^ ");\n} @*/\n" ^
                  let arg1 =
                    Str.global_replace (Str.regexp_string "bis") ""
                      (List.nth_exn args 1)
                  in
                  "/*@ { \n\
                   assert mapp<" ^ ityp ^
                  ">(_, _, _, _, mapc(_, _, ?dm_addrs)); \n\
                   assert vectorp<" ^ ityp ^
                  ">(_, _, _, ?dv_addrs); \n\
                   assert map_vec_chain_coherent<" ^ ityp ^
                  ">(?the_dm, ?the_dv, ?the_dh);\n\
                  " ^ ityp ^ " vvv = " ^ (construct_record arg1 entry_type) ^
                  "; \n\
                   mvc_coherent_key_abscent(the_dm, the_dv, the_dh, vvv);\n\
                   kkeeper_add_one(dv_addrs, the_dv, dm_addrs, vvv, " ^
                  (List.nth_exn args 2) ^
                  "); \n\
                   } @*/\n"
                else "")
            else
              None))
        with
        | Some x -> x
        | None -> "Error: unexpected argument type: " ^
                  (ttype_to_str (List.nth_exn arg_types 1))
              );];
   lemmas_after = [
     (fun {args;tmp_gen;arg_types;_} ->
        match (List.find_map map_specs ~f:(fun {typ;entry_type;coherent;_} ->
            if (List.nth_exn arg_types 1) = (Ptr entry_type) then
              Some ((if coherent then
                       let arg1 =
                         Str.global_replace (Str.regexp_string "bis") ""
                           (List.nth_exn args 1)
                       in
                       "\n/*@ {\n\
                        assert map_vec_chain_coherent<" ^ ityp_name typ ^
                       ">(" ^ (tmp_gen "dm") ^
                       ", ?" ^ (tmp_gen "dv") ^
                       ", ?" ^ (tmp_gen "dh") ^
                       ");\n\
                       " ^ ityp_name typ ^ " " ^
                       (tmp_gen "ea") ^ " = " ^
                       (construct_record arg1 entry_type) ^
                       ";\n\
                        mvc_coherent_put<" ^ ityp_name typ ^ ">(" ^
                       (tmp_gen "dm") ^
                       ", " ^ (tmp_gen "dv") ^
                       ", " ^ (tmp_gen "dh") ^
                       ", " ^ (List.nth_exn args 2) ^
                       ", time_for_allocated_index, " ^ (tmp_gen "ea") ^
                       ");\n\
                        } @*/\n" ^
                       "last_map_accessed = " ^ lma_literal_name typ ^ ";\n"
                     else "") ^
                    (String.concat ~sep:"" (List.map (other_specs typ)
                                              ~f:(fun {typ;_} ->
                                                  "//@ open hide_mapp<" ^
                                                  ityp_name typ ^
                                                  ">(_, _, _, _, _);\n"))))
            else
              None))
        with
        | Some x -> x
        | None -> "Error: unexpected argument type: " ^
                  (ttype_to_str (List.nth_exn arg_types 1)));];}

let map_erase_spec (map_specs : map_spec list) =
  let other_specs excl_typ =
    List.filter map_specs ~f:(fun {typ;_} ->
        typ <> excl_typ)
  in
  {ret_type = Static Void;
   arg_types = [Static (Ptr map_struct);
                Dynamic (List.map map_specs ~f:(fun {typ;entry_type;_} ->
                  typ, Ptr entry_type););
                Dynamic (List.map map_specs ~f:(fun {typ;entry_type;_} ->
                  typ, Ptr (Ptr entry_type));)];
   extra_ptr_types = [];
   lemmas_before = [
     (fun {args;tmp_gen;arg_types;_} ->
        match (List.find_map map_specs
                 ~f:(fun {typ;entry_type;coherent;invariant;_} ->
            if (List.nth_exn arg_types 1) = (Ptr entry_type) then
              Some (
                (String.concat ~sep:""
                   (List.map (other_specs typ)
                      ~f:(fun {typ;_} ->
                          "//@ close hide_mapp<" ^ ityp_name typ ^
                          ">(_, _, _, _, _);\n"
                        ))) ^
                (match invariant with
                 | Some invariant ->
                  let ityp = ityp_name typ in
                  let arg1 =
                    Str.global_replace (Str.regexp_string "bis") ""
                      (List.nth_exn args 1)
                  in
                  "/*@ { \n\
                   assert mapp<" ^ ityp ^
                  ">(_, _, _, _, mapc(_, ?dm, _)); \n\
                   assert " ^ pred_name typ ^
                  "(" ^ arg1 ^ ", ?" ^ tmp_gen "key" ^
                  ");\n\
                   map_erase_keep_inv(dm, " ^
                  (tmp_gen "key") ^ ",(" ^
                  (logic_name invariant) ^
                  ")(initial_time));\n\
                   } @*/\n"
                 | None -> "")
                ^
                if coherent then
                  let ityp = ityp_name typ in
                  let arg1 =
                    Str.global_replace (Str.regexp_string "bis") ""
                      (List.nth_exn args 1)
                  in
                  "/*@ { \n\
                   assert mapp<" ^ ityp ^
                  ">(_, _, _, _, mapc(_, ?dm, ?dm_addrs)); \n\
                   assert vectorp<" ^ ityp ^
                  ">(_, _, _, ?dv_addrs); \n\
                   assert map_vec_chain_coherent<" ^ ityp ^
                  ">(?the_dm, ?the_dv, ?the_dh);\n\
                   assert LoadBalancedFlowp(" ^ arg1 ^
                  ", ?vvv);\n\
                   kkeeper_erase_one(dv_addrs, the_dv, dm_addrs, map_get_fp(dm, vvv));\n\
                   } @*/\n"
                else "")
            else
              None))
        with
        | Some x -> x
        | None -> "Error: unexpected argument type: " ^
                  (ttype_to_str (List.nth_exn arg_types 1))
              );];
   lemmas_after = [
     (fun {args;tmp_gen;arg_types;_} ->
        match (List.find_map map_specs ~f:(fun {typ;entry_type;_} ->
            if (List.nth_exn arg_types 1) = (Ptr entry_type) then
              Some ((String.concat ~sep:""
                       (List.map (other_specs typ)
                          ~f:(fun {typ;_} ->
                              "//@ open hide_mapp<" ^ ityp_name typ ^
                              ">(_, _, _, _, _);\n"))))
            else
              None))
        with
        | Some x -> x
        | None -> "Error: unexpected argument type: " ^
                  (ttype_to_str (List.nth_exn arg_types 1)));];}


let expire_items_single_map_spec typs vecs (maps : map_spec list) =
  let other_types excl_typ =
    List.filter typs ~f:(fun typ ->
        typ <> excl_typ)
  in
  let other_vec_types excl_typ =
    List.filter vecs ~f:(fun {typ;_} -> typ <> excl_typ)
  in
  {ret_type = Static Sint32;
   arg_types = stt [Ptr dchain_struct;
                    Ptr vector_struct;
                    Ptr map_struct;
                    vigor_time_t];
   extra_ptr_types = [];
   lemmas_before = [
     (fun {tmp_gen;args;_} ->
        "//@ assert double_chainp(?" ^
        (tmp_gen "cur_ch") ^ ", " ^ (List.nth_exn args 0) ^ ");\n" ^
        "//@ expire_olds_keeps_high_bounded(" ^
        (tmp_gen "cur_ch") ^ ", " ^ (List.nth_exn args 3) ^ ");\n");
     (fun {tmp_gen;args;_} ->
        "switch(expire_items_single_map_order) {\n" ^
        (String.concat ~sep:""
           (List.mapi typs ~f:(fun i typ ->
                " case " ^ (string_of_int i) ^ ":\n" ^
                (String.concat ~sep:""
                   (List.map (other_types typ)
                      ~f:(fun other_typ ->
                          "//@ close hide_mapp<" ^ ityp_name other_typ ^
                          ">(_, _, _, _, _);\n"
                        ))) ^
                (String.concat ~sep:""
                   (List.map (other_vec_types typ)
                      ~f:(fun {typ;_} ->
                          "//@ close hide_vector<" ^
                          ityp_name typ ^ ">(_, _, _, _);\n"
                        ))) ^ "//@ assert vectorp<" ^ ityp_name typ ^
                ">(" ^
                (List.nth_exn args 1) ^
                ", " ^ pred_name typ ^ ", ?" ^ (tmp_gen "vec") ^ ", ?" ^
                (tmp_gen "veca") ^
                ");\n" ^
                (match List.find_map vecs ~f:(fun v ->
                     if v.typ = typ then Option.map ~f:(fun inv -> (v.name, inv)) v.invariant else None)
                 with
                 | Some (name, invariant) ->
                   "//@ vector_erase_all_keep_inv(" ^ (tmp_gen "vec") ^
                   ", dchain_get_expired_indexes_fp(" ^
                   (tmp_gen "cur_ch") ^ ", " ^
                   (List.nth_exn args 3) ^
                   "), (" ^ (logic_name invariant) ^ ")(recent_time_" ^ name ^ "));\n"
                 | None -> "") ^
                (match List.find_map maps ~f:(fun m ->
                     if m.typ = typ then m.invariant else None)
                 with
                 | Some invariant ->
                   "//@assert mapp(" ^ (List.nth_exn args 2) ^
                   ", _, _, _, mapc(_, ?" ^ (tmp_gen "fm") ^
                   ", _));\n" ^
                   "//@ map_erase_all_keep_inv(" ^ (tmp_gen "fm") ^
                   ", vector_get_values_fp(" ^ (tmp_gen "vec") ^ ", dchain_get_expired_indexes_fp(" ^
                   (tmp_gen "cur_ch") ^ ", " ^
                   (List.nth_exn args 3) ^
                   ")), (" ^ (logic_name invariant) ^ ")(initial_time));\n"
                 | None -> "") ^
                   "break;\n"
              )) ) ^
        "default:\n\
         assert false;\n\
         }\n");
     (fun {args;tmp_gen;_} ->
        "/*@ {\n\
         expire_preserves_index_range(" ^
        (tmp_gen "cur_ch") ^ ", " ^
        (List.nth_exn args 3) ^
        ");\n\
         length_nonnegative(\
         dchain_get_expired_indexes_fp(" ^
        (tmp_gen "cur_ch") ^ ", " ^
        (List.nth_exn args 3) ^
        "));\n\
         expire_old_dchain_nonfull_maybe\
         (" ^ (List.nth_exn args 0) ^ ", " ^
        (tmp_gen "cur_ch") ^ ", " ^
        (List.nth_exn args 3) ^
        ");\n" ^
         "} @*/");
   ];
   lemmas_after = [
     (fun {tmp_gen;_} ->
        "switch(expire_items_single_map_order) {\n" ^
        (String.concat ~sep:"" (List.mapi typs ~f:(fun i typ ->
             let ityp = ityp_name typ in
             " case " ^ (string_of_int i) ^ ":\n" ^
             "/*@ {\n\
              assert mapp<" ^ ityp ^ ">(_, _, _, _, mapc(_, ?" ^ (tmp_gen "fm") ^
             ", _));\n\
              assert map_vec_chain_coherent<" ^ ityp ^ ">(" ^
             (tmp_gen "fm") ^ ", ?" ^
             (tmp_gen "fvk") ^ ", ?" ^
             (tmp_gen "ch") ^
             ");\n\
              mvc_coherent_same_len<" ^ ityp ^ ">(" ^
             (tmp_gen "fm") ^ ", " ^
             (tmp_gen "fvk") ^ ", " ^
             (tmp_gen "ch") ^ ");\n} @*/\n" ^
             (String.concat ~sep:""
                (List.map (other_types typ) ~f:(fun other_typ ->
                     "//@ open hide_mapp<" ^ ityp_name other_typ ^
                     ">(_, _, _, _, _);\n"
                   ))) ^
             (String.concat ~sep:""
                (List.map (other_vec_types typ)
                   ~f:(fun {typ;_} ->
                       "//@ open hide_vector<" ^
                       ityp_name typ ^ ">(_, _, _, _);\n"
                     ))) ^
               "break;\n"
           )) ) ^
        "default:\n\
         assert false;\n\
         }\n" ^
     "expire_items_single_map_order += 1;");
   ];}

let dchain_allocate_new_index_spec dchain_specs =
  {ret_type = Static Sint32;
   arg_types = stt [Ptr dchain_struct; Ptr Sint32; vigor_time_t;];
   extra_ptr_types = [];
   lemmas_before = [
     capture_chain "cur_ch" 0;
   ];
   lemmas_after = [
     (fun {args;_} ->
        "time_for_allocated_index = " ^ (List.nth_exn args 2) ^
        ";\n");
     (fun params ->
          "/*@ if(" ^ params.ret_name ^ " != 0) " ^
          "{\n allocate_preserves_index_range(" ^
          (params.tmp_gen "cur_ch") ^
          ", *" ^
          (List.nth_exn params.args 1) ^ ", " ^
          (List.nth_exn params.args 2) ^ ");\n} @*/");
     (fun params ->
        "//@ allocate_keeps_high_bounded(" ^
        (params.tmp_gen "cur_ch") ^
        ", *" ^ (List.nth_exn params.args 1) ^
        ", " ^ (List.nth_exn params.args 2) ^
        ");\n");
     (fun params ->
        "the_index_allocated = *" ^
        (List.nth_exn params.args 1) ^ ";\n");
     (fun {args;tmp_gen;ret_name;_} ->
        "switch(last_map_accessed) {" ^
        (String.concat ~sep:""
           (List.map dchain_specs ~f:(fun typ ->
                " case " ^ lma_literal_name typ ^ ":\n" ^
                "/*@ if (" ^ ret_name ^
                " != 0) {\n\
                 assert map_vec_chain_coherent<" ^
                ityp_name typ ^ ">(?" ^
                (tmp_gen "cur_map") ^ ", ?" ^
                (tmp_gen "cur_vec") ^ ", " ^
                (tmp_gen "cur_ch") ^
                ");\n\
                 mvc_coherent_alloc_is_halfowned<" ^ ityp_name typ ^
                ">(" ^
                (tmp_gen "cur_map") ^ ", " ^
                (tmp_gen "cur_vec") ^ ", " ^
                (tmp_gen "cur_ch") ^ ", *" ^
                (List.nth_exn args 1) ^ ");\n} @*/\n" ^
                "break;\n"))) ^
        "default:\nassert false;\nbreak;\n}\n");
   ];}

let dchain_rejuvenate_index_spec dchain_specs =
  {ret_type = Static Sint32;
   arg_types = stt [Ptr dchain_struct; Sint32; vigor_time_t;];
   extra_ptr_types = [];
   lemmas_before = [
     capture_chain "cur_ch" 0;
     (fun {args;tmp_gen;_} ->
        "switch(last_map_accessed) {" ^
        (String.concat ~sep:""
           (List.map dchain_specs ~f:(fun typ ->
                " case " ^ lma_literal_name typ ^ ":\n" ^
                "/*@ {\n\
                 assert map_vec_chain_coherent<" ^
                ityp_name typ ^ ">(?" ^
                (tmp_gen "cur_map") ^ ", ?" ^
                (tmp_gen "cur_vec") ^ ", " ^
                (tmp_gen "cur_ch") ^
                ");\n\
                 mvc_coherent_same_len(" ^
                (tmp_gen "cur_map") ^ ", " ^
                (tmp_gen "cur_vec") ^ ", " ^
                (tmp_gen "cur_ch") ^ ");\n" ^
                "rejuvenate_keeps_high_bounded(" ^
                (tmp_gen "cur_ch") ^
                ", " ^ (List.nth_exn args 1) ^
                ", " ^ (List.nth_exn args 2) ^
                ");\n} @*/\n" ^
                "break;\n"
              ))) ^
        "default:\nassert false;\nbreak;\n}\n"
     );];
   lemmas_after = [
     (fun {args;ret_name;_} ->
        "switch(last_map_accessed) {" ^
        (String.concat ~sep:"" (List.map dchain_specs ~f:(fun typ ->
             " case " ^ lma_literal_name typ ^ ":\n" ^
             "/*@ if (" ^ ret_name ^
             " != 0) { \n" ^
             "assert map_vec_chain_coherent<" ^ ityp_name typ ^
             ">\
              (?cur_map,?cur_vec,?cur_ch);\n" ^
             "mvc_rejuvenate_preserves_coherent(cur_map,\
              cur_vec, cur_ch, " ^
             (List.nth_exn args 1) ^ ", "
             ^ (List.nth_exn args 2) ^
             ");\n\
              rejuvenate_preserves_index_range(cur_ch," ^
             (List.nth_exn args 1) ^ ", " ^
             (List.nth_exn args 2) ^ ");\n }@*/" ^
             "break;\n"))) ^
        "default:\nassert false;\nbreak;\n}\n");];}

let dchain_free_index_spec dchain_specs =
  {ret_type = Static Sint32;
   arg_types = stt [Ptr dchain_struct; Sint32;];
   extra_ptr_types = [];
   lemmas_before = [
     capture_chain "cur_ch" 0;
     (fun {args;tmp_gen;_} ->
        "switch(last_map_accessed) {" ^
        (String.concat ~sep:"" (List.map dchain_specs ~f:(fun typ ->
             " case " ^ lma_literal_name typ ^ ":\n" ^
             "//@ assert map_vec_chain_coherent<" ^ ityp_name typ ^ ">(?" ^
             (tmp_gen "map") ^ ", ?" ^
             (tmp_gen "vec") ^ ", " ^
             (tmp_gen "cur_ch") ^ ");\n" ^
             "//@ mvc_coherent_erase(" ^
             (tmp_gen "map") ^ ", " ^
             (tmp_gen "vec") ^ ", " ^
             (tmp_gen "cur_ch") ^ ", " ^ lsim_variable_name typ ^ ");\n" ^
             "//@ remove_index_keeps_high_bounded(" ^
             (tmp_gen "cur_ch") ^ ", " ^
             (List.nth_exn args 1) ^ ");\n" ^
             "//@ dchain_remove_keeps_ir(" ^
             (tmp_gen "cur_ch") ^ ", allocated_index_0);\n" ^
             "break;\n"
           ))) ^
        "default:\nassert false;\nbreak;\n}\n"
     );];
   lemmas_after = [];}

let dchain_is_index_allocated_spec =
  {ret_type = Static Sint32;
   arg_types = stt [Ptr dchain_struct;
                    Sint32];
   extra_ptr_types = [];
   lemmas_before = [];
   lemmas_after = [];}

let map_size_spec =
  {ret_type = Static Sint32;
   arg_types = [Static (Ptr map_struct);];
   extra_ptr_types = [];
   lemmas_before = [];
   lemmas_after = [];}

let nf_set_rte_ipv4_udptcp_checksum_spec =
  {ret_type = Static Void;
   arg_types = stt [Ptr rte_ipv4_hdr_struct;
                    Ptr tcpudp_hdr_struct;
                    Ptr Sint8];
   extra_ptr_types = [];
   lemmas_before = [];
   lemmas_after = [];}

let cht_find_preferred_available_backend_spec =
  {ret_type = Static Sint32;
   arg_types = stt [Uint64;
                    Ptr vector_struct;
                    Ptr dchain_struct;
                    Uint32;
                    Uint32;
                    Ptr Sint32];
   extra_ptr_types = [];
   lemmas_before = [];
   lemmas_after = [];}

let cht_fill_cht_spec =
  {ret_type = Static Sint32;
   arg_types = [Static (Ptr vector_struct);
                Static Sint32;
                Static Sint32];
   extra_ptr_types = [];
   lemmas_before = [(fun {args;} ->
       "//@ div_rem(" ^ (List.nth_exn args 1) ^
       ", " ^ (List.nth_exn args 1) ^ ");\n"
     )];
   lemmas_after = []}

let gen_lma_literals containers =
  (List.filter_map containers ~f:(fun (_, cnt_t) ->
       match cnt_t with
       | Map (name, _, _) -> Some (lma_literal_name name)
       | _ -> None))

let gen_dchain_params containers =
  List.filter_map containers ~f:(fun (_, ctyp) ->
       match ctyp with
         | EMap (typ, _, _, chain) -> Some typ
         | _ -> None)

let gen_preamble nf_loop containers =
  let lma_literals = gen_lma_literals containers in
  "\
#include \"libvig/verified/expirator.h\"\n\
#include \"libvig/verified/map.h\"\n\
#include \"libvig/verified/double-chain.h\"\n\
#include \"libvig/models/verified/vigor-time-control.h\"\n\
#include \"" ^ nf_loop ^ "\"\n" ^
  (In_channel.read_all "preamble.tmpl") ^
  "enum LMA_enum {" ^ (match lma_literals with | _ :: _ ->
      (String.concat ~sep:", " lma_literals) ^ ", " | _ -> "") ^
  "LMA_INVALID};\n" ^
  "void to_verify()\n\
   /*@ requires true; @*/ \n\
   /*@ ensures true; @*/\n{\n\
   uint16_t received_on_port;\n\
   int the_index_allocated = -1;\n\
   int64_t time_for_allocated_index = 0;\n\
   uint32_t packet_size = 0;\n\
   vigor_time_t initial_time = 0;\n\
   bool a_packet_received = false;\n" ^
  (String.concat ~sep:""
     (List.map (concrete_containers containers) ~f:(fun (name,ctyp) ->
          match ctyp with
          | Map (typ, _, _) ->
            "//@ list<pair<" ^ (ityp_name typ) ^ ", int> > initial_" ^ name ^ ";\n" ^
            "//@ struct Map* " ^ name ^ "_ptr;\n"
          | Vector (typ, _, _) ->
            "//@ list<pair<" ^ (ityp_name typ) ^ ", real> > initial_" ^ name ^ ";\n" ^
            "//@ struct Vector* " ^ name ^ "_ptr;\n" ^
            "vigor_time_t recent_time_" ^ name ^ " = 0;\n"
          | CHT (_, _) ->
            "//@ list<pair<uint32_t, real> > initial_" ^ name ^ ";\n" ^
            "//@ struct Vector* " ^ name ^ "_ptr;\n"
          | DChain _ ->
            "//@ dchain initial_" ^ name ^ ";\n" ^
            "//@ struct DoubleChain* " ^ name ^ "_ptr;\n"
          | Int
          | UInt
          | UInt32 -> "//@ int " ^ name ^ ";\n"
          | EMap (_, _, _, _) -> "#error only concrete containers at this point"
          | LPM _ ->
            "//@ dir_24_8 initial_" ^ name ^ ";\n" ^
            "//@ struct lpm* " ^ name ^ "_ptr;\n"
        ))) ^
  "//@ option<void*> last_composed_packet = none;\n\
   //@ bool packet_is_complete = false;\n\
   //@ list<uint8_t> last_sent_packet = nil;\n\
   //@ list<phdr> recv_headers = nil; \n\
   //@ list<phdr> sent_headers = nil; \n\
   //@ list<uint16_t> sent_on_ports = nil; \n\
   //@ assume(sizeof(struct rte_ether_hdr) == 14);\n\
   //@ assume(sizeof(struct tcpudp_hdr) == 4);\n\
   //@ assume(sizeof(struct rte_ipv4_hdr) == 20);\
   //TODO: handle all this sizeof's explicitly\n"
  ^
  "int vector_allocation_order = 0;\n\
   int map_allocation_order = 0;\n\
   int dchain_allocation_order = 0;\n\
   int expire_items_single_map_order = 0;\n\
   enum LMA_enum last_map_accessed = " ^
  (match lma_literals with | hd :: _ -> hd | _ -> "0") ^ ";\n" ^
  (String.concat ~sep:"" (List.map containers ~f:(fun (_,ctyp) ->
       match ctyp with
       | EMap (typ, _, _, _) -> "//@ " ^ (ityp_name typ) ^ " " ^
                                (lsim_variable_name typ) ^ ";\n"
       | _ -> ""
     )))

let gen_map_params containers records =
  let is_map_coherent map = List.exists containers ~f:(fun (_,ctyp) ->
      match ctyp with
      | EMap (_, emap_map, _, _) -> map = emap_map
      | _ -> false)
  in
  List.filter_map containers ~f:(fun (name,ctyp) ->
      match ctyp with
      | Map (typ, _, invariant) ->
        Some {typ;coherent=is_map_coherent name;
              entry_type=String.Map.find_exn records typ;
              invariant=if invariant = "" then None else Some invariant}
      | _ -> None)

let abstract_state_capture containers =
  (String.concat ~sep:"" (List.mapi containers ~f:(fun i (name,t) ->
       match t with
       | Map (typ, _, _) -> "assert mapp<" ^ (ityp_name typ) ^ ">(" ^
                            name ^ "_ptr, _, _, _, mapc(_, ?" ^
                            ("final_" ^ name) ^ ", _));\n" ^
                            "list<pair<" ^ (ityp_name typ) ^ ", int> > " ^
                            name ^ " = initial_" ^ name ^ ";\n"
       | Vector (typ, _, _) -> "assert vectorp<" ^ (ityp_name typ) ^ ">(" ^
                               name ^ "_ptr, _, ?" ^
                               ("finalizing_final_" ^ name) ^ ", _);\n" ^
                               "vector<" ^ (ityp_name typ) ^ "> " ^ name ^
                               " = vector(" ^ "initial_" ^ name ^ ");\n" ^
                               "vector<" ^ (ityp_name typ) ^ "> final_" ^ name ^
                               " = vector(" ^ "finalizing_final_" ^ name ^ ");\n"
       | CHT (_, _) -> "assert vectorp<uint32_t>(" ^
                       name ^ "_ptr, _, ?" ^
                       ("final_" ^ name) ^ ", _);\n" ^
                       "list<pair<uint32_t, real> > " ^ name ^ " = " ^
                       "initial_" ^ name ^ ";\n"
       | DChain _ -> "assert double_chainp(?" ^ "final_" ^ name ^ ", " ^
                     name ^ "_ptr);\n" ^
                     "dchain " ^ name ^ " = " ^ ("initial_" ^ name) ^ ";\n"
       | Int
       | UInt
       | UInt32 -> ""
       | EMap (typ, m, v, h) -> "emap<" ^ (ityp_name typ) ^ "> " ^ name ^
                                " = emap<" ^ (ityp_name typ) ^ ">(" ^ m ^
                                ", initial_" ^ v ^ ", " ^ h ^ ");\n" ^
                                "emap<" ^ (ityp_name typ) ^ "> final_" ^ name ^
                                " = emap<" ^ (ityp_name typ) ^ ">(final_" ^ m ^
                                ", finalizing_final_" ^ v ^ ", final_" ^ h ^
                                ");\n"
       | LPM _ -> "assert table(" ^
                  name ^ "_ptr, ?" ^
                  ("final_" ^ name) ^ ");\n" ^
                  "dir_24_8 " ^
                  name ^ " = initial_" ^ name ^ ";\n"
     )))

let fun_types containers records =
  String.Map.of_alist_exn
    (common_fun_types @
     (List.filter_map
        (String.Map.data records) ~f:(fun record -> match record with
            | Str (_, _) -> Some (hash_spec record)
            | _ -> None )) @
    ["loop_invariant_consume", (loop_invariant_consume_spec containers records);
     "loop_invariant_produce", (loop_invariant_produce_spec containers);
     "dchain_allocate", (dchain_alloc_spec (gen_dchain_params containers));
     "dchain_allocate_new_index", (dchain_allocate_new_index_spec
                                     (gen_dchain_params containers));
     "dchain_rejuvenate_index", (dchain_rejuvenate_index_spec
                                   (gen_dchain_params containers));
     "dchain_free_index", (dchain_free_index_spec
                             (gen_dchain_params containers)) ;
     "dchain_is_index_allocated", dchain_is_index_allocated_spec;
     "expire_items_single_map", (expire_items_single_map_spec
                                   (gen_dchain_params containers)
                                   (gen_vector_params containers records)
                                   (gen_map_params containers records));
     "map_allocate", (map_alloc_spec
                        (gen_map_params containers records));
     "map_get", (map_get_spec (gen_map_params containers records));
     "map_put", (map_put_spec (gen_map_params containers records));
     "map_erase", (map_erase_spec (gen_map_params containers records));
     "map_size", map_size_spec;
     "cht_fill_cht", cht_fill_cht_spec;
     "nf_set_rte_ipv4_udptcp_checksum", nf_set_rte_ipv4_udptcp_checksum_spec;
     "cht_find_preferred_available_backend",
     cht_find_preferred_available_backend_spec;
     "vector_allocate", (vector_alloc_spec
                           (gen_vector_params containers records));
     "vector_borrow", (vector_borrow_spec
                         (gen_vector_params containers records));
     "vector_return", (vector_return_spec
                         (gen_vector_params containers records));])

