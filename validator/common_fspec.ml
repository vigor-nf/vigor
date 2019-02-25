open Core
open Str
open Fspec_api
open Ir


let map_struct = Ir.Str ("Map", [])
let vector_struct = Ir.Str ( "Vector", [] )
let dchain_struct = Ir.Str ( "DoubleChain", [] )

let ether_addr_struct = Ir.Str ( "ether_addr", ["addr_bytes", Array Uint8;])
let ether_hdr_struct = Ir.Str ("ether_hdr", ["d_addr", ether_addr_struct;
                                             "s_addr", ether_addr_struct;
                                             "ether_type", Uint16;])
let ipv4_hdr_struct = Ir.Str ("ipv4_hdr", ["version_ihl", Uint8;
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
let tcp_hdr_struct = Ir.Str ("tcp_hdr", ["src_port", Uint16;
                                         "dst_port", Uint16;
                                         "sent_seq", Uint32;
                                         "recv_ack", Uint32;
                                         "data_off", Uint8;
                                         "tcp_flags", Uint8;
                                         "rx_win", Uint16;
                                         "cksum", Uint16;
                                         "tcp_urp", Uint16;])

let stub_mbuf_content_struct = Ir.Str ( "stub_mbuf_content",
                                        ["ether", ether_hdr_struct;
                                         "ipv4", ipv4_hdr_struct;
                                         "tcp", tcp_hdr_struct;])

let rte_mempool_struct = Ir.Str ( "rte_mempool", [] )
let rte_mbuf_struct = Ir.Str ( "rte_mbuf",
                               ["buf_addr", Ptr stub_mbuf_content_struct;
                                "buf_iova", Uint64;
                                "data_off", Uint16;
                                "refcnt", Uint16;
                                "nb_segs", Uint16;
                                "port", Uint16;
                                "ol_flags", Uint64;
                                "packet_type", Uint32;
                                "pkt_len", Uint32;
                                "data_len", Uint16;
                                "vlan_tci", Uint16;
                                "hash", Uint32;
                                "vlan_tci_outer", Uint16;
                                "buf_len", Uint16;
                                "timestamp", Uint64;
                                "udata64", Uint64;
                                "pool", Ptr rte_mempool_struct;
                                "next", Ptr Void;
                                "tx_offload", Uint64;
                                "priv_size", Uint16;
                                "timesync", Uint16; 
                                "seqn", Uint32] )

let noop _ = ""

let capture_a_map t name {tmp_gen;_} =
  "//@ assert mapp<" ^ t ^ ">(_, _, _, _, mapc(_,?" ^ (tmp_gen name) ^ ", _));\n"

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
                      arg_types = stt [Uint16; Ptr (Ptr Sint8); Ptr Uint16];
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
                       let packet_ptr = (render_tterm (List.nth_exn arg_exps 0)) in
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
                       "sent_on_ports = cons((uint16_t)" ^ (List.nth_exn args 1) ^ ", sent_on_ports);\n" 
                     )];};
   "packet_borrow_next_chunk", {ret_type = Static Void;
                                arg_types = [Static (Ptr Sint8);
                                             Static Uint32;
                                             Dynamic ["ether_hdr",
                                                      Ptr (Ptr ether_hdr_struct);
                                                      "ipv4_hdr",
                                                      Ptr (Ptr ipv4_hdr_struct);
                                                      "tcpudp_hdr",
                                                      Ptr (Ptr tcpudp_hdr_struct);
                                                      "ipv4_options",
                                                      Ptr (Ptr Sint8)
                                                     ]];
                                extra_ptr_types =
                                  ["the_chunk",
                                   Dynamic ["ether_hdr",
                                            Ptr ether_hdr_struct;
                                            "ipv4_hdr",
                                            Ptr ipv4_hdr_struct;
                                            "tcpudp_hdr",
                                            Ptr tcpudp_hdr_struct;
                                            "ipv4_options",
                                            Ptr Sint8
                                           ]];
                                lemmas_before = [(fun _ -> "//@ packet_is_complete = false;")];
                                lemmas_after = [
                                  (fun {args;arg_types;_} ->
                                     match (List.nth_exn arg_types 2) with
                                     | Ptr (Ptr (Str (_,_))) ->
                                       "//@ close_struct(*" ^ (List.nth_exn args 2) ^ ");\n"
                                     | _ -> ""
                                  );
                                  (fun {args;arg_types;_} ->
                                     match List.nth_exn arg_types 2 with
                                     | Ptr (Ptr (Str ("ether_hdr", _))) ->
                                       "//@ recv_headers = add_ether_header(recv_headers, *" ^ (List.nth_exn args 2) ^ ");\n" ^
                                       "//@ open ether_hdrp(*" ^ (List.nth_exn args 2) ^
                                       ", _);\n\
                                        //@ open ether_addrp((" ^ (List.nth_exn args 2) ^
                                       "->s_addr), _);\n\
                                        //@ open ether_addrp((" ^ (List.nth_exn args 2) ^
                                       "->d_addr), _);\n"
                                     | Ptr (Ptr (Str ("ipv4_hdr", _))) ->
                                       "//@ recv_headers = add_ipv4_header(recv_headers, *" ^ (List.nth_exn args 2) ^ ");\n"
                                     | Ptr (Ptr (Str ("tcpudp_hdr", _))) ->
                                       "//@ recv_headers = add_tcpudp_header(recv_headers, *" ^ (List.nth_exn args 2) ^ ");\n"
                                     | Ptr (Ptr Sint8) ->
                                       ""
                                     | _ -> failwith "unsupported chunk type in packet_borrow_next_chunk"
                                  )];};
   "packet_return_chunk", {ret_type = Static Void;
                           arg_types = [Static (Ptr Sint8);
                                        Dynamic ["ether_hdr",
                                                 Ptr ether_hdr_struct;
                                                 "ipv4_hdr",
                                                 Ptr ipv4_hdr_struct;
                                                 "tcpudp_hdr",
                                                 Ptr tcpudp_hdr_struct;
                                                 "ipv4_options",
                                                 Ptr Sint8
                                                ]];
                           extra_ptr_types = [];
                           lemmas_before = [
                             (fun {arg_exps;arg_types;_} ->
                                match List.nth_exn arg_types 1 with
                                | Ptr (Str ("ether_hdr", _)) ->
                                  "//@ sent_headers = add_ether_header(sent_headers, " ^
                                  (render_tterm (List.nth_exn arg_exps 1)) ^
                                  ");\n\
                                   //@ open ether_hdrp(" ^
                                  (render_tterm (List.nth_exn arg_exps 1)) ^
                                  ", _);\n\
                                   //@ open ether_addrp(&(" ^
                                  (render_tterm (List.nth_exn arg_exps 1)) ^
                                  "->s_addr), _);\n\
                                   //@ open ether_addrp(&(" ^
                                  (render_tterm (List.nth_exn arg_exps 1)) ^
                                  "->d_addr), _);\n"
                                | Ptr (Str ("ipv4_hdr", _)) ->
                                  "//@ sent_headers = add_ipv4_header(sent_headers, " ^
                                  (render_tterm (List.nth_exn arg_exps 1)) ^
                                  ");\n"
                                | Ptr (Str ("tcpudp_hdr", _)) ->
                                  "//@ sent_headers = add_tcpudp_header(sent_headers, " ^
                                  (render_tterm (List.nth_exn arg_exps 1)) ^
                                  ");\n"
                                | Ptr Sint8 ->
                                  ""
                                | _ -> failwith "unsupported chunk type in packet_return_chunk"
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
                               let packet_ptr = (render_tterm (List.nth_exn arg_exps 0)) in
                               "char* " ^ (tmp_gen "synonym") ^ " = " ^ packet_ptr ^
                               ";\n/*@ {\n assert packetp(" ^ (tmp_gen "synonym") ^
                               ", _, ?unreturned_chunks);\n\
                                switch(last_composed_packet) {\n\
                                case none:\n\
                                last_composed_packet = some(" ^ packet_ptr ^
                               ");\n\
                                case some(cp):\n\
                                assert cp == " ^ packet_ptr ^
                               ";\n};\n\
                                packet_is_complete = (unreturned_chunks == nil);\n \
                                }\n@*/"
                             )];};
   "packet_get_unread_length", {ret_type = Static Uint32;
                                arg_types = stt [Ptr Sint8];
                                extra_ptr_types = [];
                                lemmas_before = [];
                                lemmas_after = [];};
   "packet_state_total_length", {ret_type = Static Void;
                                 arg_types = stt [Ptr Sint8;
                                                  Ptr Uint16];
                                 extra_ptr_types = [];
                                 lemmas_before = [];
                                 lemmas_after = [];};
   "packet_free", {ret_type = Static Void;
                   arg_types = stt [Ptr Sint8;];
                   extra_ptr_types = [];
                   lemmas_before = [];
                   lemmas_after = [];};
   "packet_clone", {ret_type = Static Void;
                    arg_types = stt [Ptr Sint8;
                                     Ptr (Ptr Sint8)];
                    extra_ptr_types = [];
                    lemmas_before = [];
                    lemmas_after = [];};
  ]

let map_alloc_spec map_specs =
  {ret_type = Static Sint32;
   arg_types = stt [Fptr "map_keys_equality";
                    Fptr "map_key_hash";
                    Uint32;
                    Ptr (Ptr map_struct)];
   extra_ptr_types = [];
   lemmas_before = [
     tx_bl
       ("\n\
        switch(map_allocation_order) {\n" ^
        (String.concat ~sep:"" (List.mapi map_specs ~f:(fun i (typ,pred,eq_fun,hash_fun,lhash_fun) ->
             " case " ^ (string_of_int i) ^
             ":\n\
              produce_function_pointer_chunk \
              map_keys_equality<" ^ typ ^ ">(" ^ eq_fun ^
             ")\
              (" ^ pred ^
             ")(a, b) \
              {\
              call();\
              }\n\
              produce_function_pointer_chunk \
              map_key_hash<" ^ typ ^ ">(" ^ hash_fun ^
             ")\
              (" ^ pred ^ ", " ^ lhash_fun ^
             ")(a) \
              {\
              call();\
              }\n
              break;\n"
           )) ) ^
          "default:\n\
            assert false;\n\
        }\n");
   ];
   lemmas_after = [
     (fun {tmp_gen;_} ->
        "/*@ \n\
        switch(map_allocation_order) {\n" ^
        (String.concat ~sep:"" (List.mapi map_specs ~f:(fun i (typ,pred,eq_fun,hash_fun,lhash_fun) ->
             " case " ^ (string_of_int i) ^
             ":\n\
              assert [?" ^ (tmp_gen "imkest") ^
             "]is_map_keys_equality(" ^ eq_fun ^ ",\
              " ^ pred ^ ");\n\
              close [" ^ (tmp_gen "imkest") ^
             "]hide_is_map_keys_equality(" ^ eq_fun ^ ", \
              " ^ pred ^ ");\n\
              assert [?" ^ (tmp_gen "imkhst") ^
             "]is_map_key_hash(" ^ hash_fun ^ ",\
              " ^ pred ^ ", " ^ lhash_fun ^ ");\n\
              close [" ^ (tmp_gen "imkhst") ^
             "]hide_is_map_key_hash(" ^ hash_fun ^ ", \
              " ^ pred ^ ", " ^ lhash_fun ^ ");\n\
              break;\n"
           )) ) ^
          "default:\n\
            assert false;\n\
        }\n @*/");
     (fun _ ->
        "map_allocation_order += 1;");];}

let c_type typ =
  if typ = "uint32_t" then typ else "struct " ^ typ

let vector_alloc_spec vector_specs =
  {ret_type = Static Sint32;
   arg_types = stt [Sint32;
                    Uint32;
                    Fptr "vector_init_elem";
                    Ptr (Ptr vector_struct)];
   extra_ptr_types = [];
   lemmas_before = [
     tx_bl
       (
        "\n\
        switch(vector_allocation_order) {\n" ^
        (String.concat ~sep:"" (List.mapi vector_specs ~f:(fun i (ityp, typ, pred, alloc_fun, has_keeper) ->
             " case " ^ (string_of_int i) ^ ":\n\
              produce_function_pointer_chunk \
              vector_init_elem<" ^ ityp ^ ">(" ^ alloc_fun ^
             ")(" ^ pred ^
             ", sizeof(" ^ (c_type typ) ^
             "))(a) \
              {\
              call();\
              }\n\
              break;\n"
           )) ) ^
          "default:\n\
            assert false;\n\
        }\n");
     (fun {args;_} ->
       ("\n\
        switch(vector_allocation_order) {\n" ^
        (String.concat ~sep:"" (List.mapi vector_specs ~f:(fun i (ityp, typ, pred, alloc_fun, has_keeper) ->
             " case " ^ (string_of_int i) ^ ":\n\
               //@assume(sizeof(" ^ (c_type typ) ^ ") == " ^
             (List.nth_exn args 0) ^
             ");\n\
              break;\n"
           )) ) ^
          "default:\n\
            assert false;\n\
        }\n"));
   ];
   lemmas_after = [
     (fun {tmp_gen;ret_name;_} ->
       ("\n\
        switch(vector_allocation_order) {\n" ^
        (String.concat ~sep:"" (List.mapi vector_specs ~f:(fun i (ityp, typ, pred, alloc_fun, has_keeper) ->
             " case " ^ (string_of_int i) ^ ":\n" ^
             (if has_keeper then
                "/*@ if (" ^ ret_name ^
                ") {\n\
                 assert mapp<" ^ ityp ^ ">(_, _, _, _, mapc(?" ^ (tmp_gen "cap") ^
                ", ?" ^ (tmp_gen "map") ^
                ", ?" ^ (tmp_gen "addr_map") ^
                "));\n\
                 assert vectorp<" ^ ityp ^ ">(_, _, ?" ^ (tmp_gen "dks") ^
                ", ?" ^ (tmp_gen "dkaddrs") ^
                ");\n\
                 empty_kkeeper(" ^
                (tmp_gen "dkaddrs") ^
                ", " ^ (tmp_gen "dks") ^
                ", " ^ (tmp_gen "addr_map") ^
                ", " ^ (tmp_gen "cap") ^
                ");\n\
                 }@*/"
              else
                ""
             ) ^
              "break;\n"
           )) ) ^
          "default:\n\
            assert false;\n\
           }\n"));
     (fun _ ->
        "vector_allocation_order += 1;")];}

let vector_borrow_spec entry_specs =
  let other_types excl_ityp =
    List.filter entry_specs ~f:(fun (ityp,typ,pred,open_callback,entry_type,has_keeper) ->
        ityp <> excl_ityp)
  in
  {ret_type = Static Void;
   arg_types = [Static (Ptr vector_struct);
                Static Sint32;
                Dynamic (List.map entry_specs ~f:(fun (ityp,typ,pred,open_callback,entry_type,has_keeper) ->
                  (typ, Ptr (Ptr entry_type))));];
   extra_ptr_types = ["borrowed_cell",
                      Dynamic (List.map entry_specs ~f:(fun (ityp,typ,pred,open_callback,entry_type,has_keeper) ->
                        (typ, Ptr entry_type)));];
   lemmas_before = [
     (fun {arg_types;args;tmp_gen;_} ->
        match (List.find_map entry_specs ~f:(fun (ityp,typ,pred,open_callback,entry_type,has_keeper) ->
             if (List.nth_exn arg_types 2) = (Ptr (Ptr entry_type)) then
               Some ((String.concat ~sep:"" (List.map (other_types ityp)
                                               ~f:(fun (ityp,typ,pred,open_callback,entry_type,has_keeper) ->
                          "//@ close hide_vector<" ^ ityp ^ ">(_, _, _, _);\n"
                        ))) ^"//@ assert vectorp<" ^ ityp ^ ">(" ^ (List.nth_exn args 0) ^
                     ", " ^ pred ^ ", ?" ^ (tmp_gen "vec") ^ ", ?" ^ (tmp_gen "veca") ^
                     ");\n//@ vector_addrs_same_len_nodups(" ^ (List.nth_exn args 0) ^ ");\n" ^
                     (if has_keeper then
                        "/*@ {\n\
                         assert mapp<" ^ ityp ^ ">(_, _, _, _, mapc(_,?" ^ (tmp_gen "fm") ^
                        ", ?" ^ (tmp_gen "fma") ^
                        "));\n\
                         forall2_nth(" ^ (tmp_gen "vec") ^ ", " ^ (tmp_gen "veca") ^
                        ", (kkeeper)(" ^ (tmp_gen "fma") ^ "), " ^ (List.nth_exn args 1) ^
                        ");\n} @*/ "
                      else
                        "//@ forall_mem(nth(" ^ (List.nth_exn args 1) ^ ", " ^ (tmp_gen "vec") ^ "), " ^ (tmp_gen "vec") ^ ", is_one);"))
             else
               None
           ))
        with
        | Some x -> x
        | None -> "Error: unexpected argument type: " ^ (ttype_to_str (List.nth_exn arg_types 2)));];
   lemmas_after = [
     (fun {arg_types;args;tmp_gen;_} ->
        match (List.find_map entry_specs ~f:(fun (ityp,typ,pred,open_callback,entry_type,has_keeper) ->
            if (List.nth_exn arg_types 2) = (Ptr (Ptr entry_type)) then
              Some (String.concat ~sep:"" (List.map (other_types ityp) ~f:(fun (ityp,typ,pred,open_callback,entry_type,has_keeper) ->
                         "//@ open hide_vector<" ^ ityp ^ ">(_, _, _, _);\n")) ^
                    (open_callback (List.nth_exn args 2)))
            else
              None))
        with
        | Some x -> x
        | None -> "Error: unexpected argument type: " ^ (ttype_to_str (List.nth_exn arg_types 2)))];}

let vector_return_spec entry_specs =
  let other_types excl_ityp =
    List.filter entry_specs ~f:(fun (ityp,typ,pred,entry_type,has_keeper) ->
        ityp <> excl_ityp)
  in
  {ret_type = Static Void;
   arg_types = [Static (Ptr vector_struct);
                Static Sint32;
                Dynamic (List.map entry_specs ~f:(fun (ityp,typ,pred,entry_type,has_keeper) ->
                    (typ, Ptr entry_type)));];
   extra_ptr_types = [];
   lemmas_before = [
     (fun {arg_types;args;tmp_gen;_} ->
        match (List.find_map entry_specs ~f:(fun (ityp,typ,pred,entry_type,has_keeper) ->
            if (List.nth_exn arg_types 2) = (Ptr entry_type) then
              Some (String.concat ~sep:"" (List.map (other_types ityp) ~f:(fun (ityp,typ,pred,entry_type,has_keeper) ->
                         "//@ close hide_vector<" ^ ityp ^ ">(_, _, _, _);\n"
                       )))
            else
              None))
        with
        | Some x -> x
        | None -> "Error: unexpected argument type: " ^ (ttype_to_str (List.nth_exn arg_types 2)))];
   lemmas_after = [
     (fun {arg_types;args;tmp_gen;_} ->
        match (List.find_map entry_specs ~f:(fun (ityp,typ,pred,entry_type,has_keeper) ->
            if (List.nth_exn arg_types 2) = (Ptr entry_type) then
              Some (String.concat ~sep:"" (List.map (other_types ityp) ~f:(fun (ityp,typ,pred,entry_type,has_keeper) ->
                         "//@ open hide_vector<" ^ ityp ^ ">(_, _, _, _);\n"
                       )))
            else
              None))
        with
        | Some x -> x
        | None -> "Error: unexpected argument type: " ^ (ttype_to_str (List.nth_exn arg_types 2)))];}

let dchain_alloc_spec cap mvc_coherent_ityp =
  {ret_type = Static Sint32;
   arg_types = stt [Sint32; Ptr (Ptr dchain_struct)];
   extra_ptr_types = [];
   lemmas_before = [];
   lemmas_after =
     (tx_l ("index_range_of_empty(" ^ cap ^ ", 0);")) ::
     (match mvc_coherent_ityp with
      | Some ityp ->[
          on_rez_nonzero
            ("{\n\
              assert vectorp<" ^ ityp ^
             ">(_, _, ?allocated_vector, _);\n\
              empty_map_vec_dchain_coherent\
              <" ^ ityp ^ ">(allocated_vector);\n}")]
      | None -> []);}

let loop_invariant_consume_spec types =
  {ret_type = Static Void;
   arg_types = stt types ;
   extra_ptr_types = [];
   lemmas_before = [
     (fun {args;_} ->
        "/*@ close evproc_loop_invariant(" ^
        (String.concat ~sep:", "
           (List.map2_exn args types ~f:(fun arg t ->
                match t with
                | Ptr _ -> "*" ^ arg
                | _ -> arg
              )  )) ^ "); @*/");
   ];
   lemmas_after = [];}

let map_get_spec map_specs =
  let other_specs excl_ityp =
    List.filter map_specs ~f:(fun (ityp,typ,pred,entry_type,coherent) ->
        ityp <> excl_ityp)
  in
  {ret_type = Static Sint32;
   arg_types = [Static (Ptr map_struct);
                Dynamic (List.map map_specs ~f:(fun (ityp,typ,pred,entry_type,coherent) ->
                  typ, Ptr entry_type));
                Static (Ptr Sint32)];
   extra_ptr_types = [];
   lemmas_before = [
     (fun ({arg_exps;tmp_gen;arg_types;_} as params) ->
        match (List.find_map map_specs ~f:(fun (ityp,typ,pred,entry_type,coherent) ->
            if (List.nth_exn arg_types 1) = (Ptr entry_type) then
              Some (
                (String.concat ~sep:"" (List.map (other_specs ityp) ~f:(fun (ityp,typ,pred,entry_type,coherent) ->
                     "//@ close hide_mapp<" ^ ityp ^ ">(_, _, _, _, _);\n"
                   ))) ^
                (if coherent then
                   let (binding,expr) =
                     self_dereference (List.nth_exn arg_exps 1) tmp_gen
                   in
                   binding ^
                   "\n//@ assert " ^ pred ^ "(" ^ (render_tterm expr) ^
                   ", ?" ^ (tmp_gen "fk") ^ ");\n" ^
                   capture_a_map ityp "dm" params ^
                   "//@ assert map_vec_chain_coherent<" ^ ityp ^ ">(" ^
                   (tmp_gen "dm") ^ ", ?" ^
                   (tmp_gen "dv") ^ ", ?" ^
                   (tmp_gen "dh") ^ ");\n"
                 else ""))
            else
              None))
        with
        | Some x -> x
        | None -> "Error: unexpected argument type: " ^ (ttype_to_str (List.nth_exn arg_types 1))

     );];
   lemmas_after = [
     (fun {ret_name;tmp_gen;arg_types;_} ->
        match (List.find_map map_specs ~f:(fun (ityp,typ,pred,entry_type,coherent) ->
            if (List.nth_exn arg_types 1) = (Ptr entry_type) then
              Some ("/*@ if (" ^ ret_name ^
                    " != 0) {\n\
                     mvc_coherent_map_get_bounded(" ^
                    (tmp_gen "dm") ^ ", " ^
                    (tmp_gen "dv") ^ ", " ^
                    (tmp_gen "dh") ^ ", " ^
                    (tmp_gen "fk") ^
                    ");\n\
                     mvc_coherent_map_get_vec_half(" ^
                    (tmp_gen "dm") ^ ", " ^
                    (tmp_gen "dv") ^ ", " ^
                    (tmp_gen "dh") ^ ", " ^
                    (tmp_gen "fk") ^
                    ");\n\
                     mvc_coherent_map_get(" ^
                    (tmp_gen "dm") ^ ", " ^
                    (tmp_gen "dv") ^ ", " ^
                    (tmp_gen "dh") ^ ", " ^
                    (tmp_gen "fk") ^ ");\n} @*/\n" ^
                    (String.concat ~sep:"" (List.map (other_specs ityp) ~f:(fun (ityp,typ,pred,entry_type,coherent) ->
                         "//@ open hide_mapp<" ^ ityp ^ ">(_, _, _, _, _);\n"
                       )))
                   )
            else
              None))
        with
        | Some x -> x
        | None -> "Error: unexpected argument type: " ^ (ttype_to_str (List.nth_exn arg_types 1)));
   ];}

let map_put_spec ityp pred entry_type ctor =
  {ret_type = Static Void;
   arg_types = stt [Ptr map_struct;
                    Ptr entry_type;
                    Sint32];
   extra_ptr_types = [];
   lemmas_before = [
     (fun {args;tmp_gen;_} ->
        "\n//@ assert mapp<" ^ ityp ^ ">(_, _, _, _, mapc(_, ?" ^ (tmp_gen "dm") ^
        ", _));\n" ^
        "\n/*@ {\n\
         assert map_vec_chain_coherent<" ^ ityp ^ ">(" ^
        (tmp_gen "dm") ^ ", ?" ^
        (tmp_gen "dv") ^ ", ?" ^
        (tmp_gen "dh") ^
        ");\n\
         mvc_coherent_dchain_non_out_of_space_map_nonfull<" ^ ityp ^ ">(" ^
        (tmp_gen "dm") ^ ", " ^
        (tmp_gen "dv") ^ ", " ^
        (tmp_gen "dh") ^ ");\n" ^
        "mvc_coherent_bounds<" ^ ityp ^ ">(" ^
        (tmp_gen "dm") ^ ", " ^
        (tmp_gen "dv") ^ ", " ^
        (tmp_gen "dh") ^ ");\n} @*/\n" ^
        let arg1 = Str.global_replace (Str.regexp_string "bis") "" (List.nth_exn args 1) in
        "/*@ { \n\
         assert mapp<" ^ ityp ^ ">(_, _, _, _, mapc(_, _, ?dm_addrs)); \n\
         assert vectorp<" ^ ityp ^ ">(_, _, _, ?dv_addrs); \n\
         assert map_vec_chain_coherent<" ^ ityp ^ ">(?the_dm, ?the_dv, ?the_dh);\n\
         " ^ ityp ^ " vvv = " ^ (ctor arg1) ^ "; \n\
         mvc_coherent_key_abscent(the_dm, the_dv, the_dh, vvv);\n\
         kkeeper_add_one(dv_addrs, the_dv, dm_addrs, vvv, " ^ (List.nth_exn args 2) ^
        "); \n\
         } @*/\n"
     );];
   lemmas_after = [
     (fun {args;tmp_gen;_} ->
        let arg1 = Str.global_replace (Str.regexp_string "bis") "" (List.nth_exn args 1) in
        "\n/*@ {\n\
         assert map_vec_chain_coherent<" ^ ityp ^ ">(" ^ (tmp_gen "dm") ^
        ", ?" ^ (tmp_gen "dv") ^
        ", ?" ^ (tmp_gen "dh") ^
        ");\n\
         " ^ ityp ^ " " ^ (tmp_gen "ea") ^ " = " ^ (ctor arg1) ^ ";\n\
         mvc_coherent_put<" ^ ityp ^ ">(" ^ (tmp_gen "dm") ^
        ", " ^ (tmp_gen "dv") ^
        ", " ^ (tmp_gen "dh") ^
        ", " ^ (List.nth_exn args 2) ^
        ", time_for_allocated_index, " ^ (tmp_gen "ea") ^
        ");\n\
         } @*/\n"
     );];}

let expire_items_single_map_spec ityps =
  let other_types excl_ityp =
    List.filter ityps ~f:(fun ityp ->
        ityp <> excl_ityp)
  in
  {ret_type = Static Sint32;
   arg_types = stt [Ptr dchain_struct;
                    Ptr vector_struct;
                    Ptr map_struct;
                    vigor_time_t];
   extra_ptr_types = [];
   lemmas_before = [
     (fun _ ->
        "switch(expire_items_single_map_order) {\n" ^
        (String.concat ~sep:"" (List.mapi ityps ~f:(fun i ityp ->
             " case " ^ (string_of_int i) ^ ":\n" ^
             (String.concat ~sep:"" (List.map (other_types ityp) ~f:(fun other_ityp ->
                  "//@ close hide_mapp<" ^ other_ityp ^ ">(_, _, _, _, _);\n"
                ))) ^
              "break;\n"
           )) ) ^
        "default:\n\
         assert false;\n\
         }\n");
     (fun {tmp_gen;args;_} ->
        "//@ assert double_chainp(?" ^
        (tmp_gen "cur_ch") ^ ", " ^ (List.nth_exn args 0) ^ ");\n" ^
        "//@ expire_olds_keeps_high_bounded(" ^
        (tmp_gen "cur_ch") ^ ", " ^ (List.nth_exn args 3) ^ ");\n");
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
         if (length(dchain_get_expired_indexes_fp(" ^
        (tmp_gen "cur_ch") ^ ", " ^
        (List.nth_exn args 3) ^
        ")) > 0 ) {\n\
         expire_old_dchain_nonfull\
         (" ^ (List.nth_exn args 0) ^ ", " ^
        (tmp_gen "cur_ch") ^ ", " ^
        (List.nth_exn args 3) ^
        ");\n\
         }} @*/");
   ];
   lemmas_after = [
     (fun {tmp_gen;_} ->
        "switch(expire_items_single_map_order) {\n" ^
        (String.concat ~sep:"" (List.mapi ityps ~f:(fun i ityp ->
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
             (String.concat ~sep:"" (List.map (other_types ityp) ~f:(fun other_ityp ->
                  "//@ open hide_mapp<" ^ other_ityp ^ ">(_, _, _, _, _);\n"
                ))) ^
              "break;\n"
           )) ) ^
        "default:\n\
         assert false;\n\
         }\n" ^
     "expire_items_single_map_order += 1;");
   ];}

let dchain_allocate_new_index_spec ityp =
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
     on_rez_nz
       (fun params ->
          "{\n allocate_preserves_index_range(" ^
          (params.tmp_gen "cur_ch") ^
          ", *" ^
          (List.nth_exn params.args 1) ^ ", " ^
          (List.nth_exn params.args 2) ^ ");\n}");
     (fun params ->
        "//@ allocate_keeps_high_bounded(" ^
        (params.tmp_gen "cur_ch") ^
        ", *" ^ (List.nth_exn params.args 1) ^
        ", " ^ (List.nth_exn params.args 2) ^
        ");\n");
     (fun params ->
        "the_index_allocated = *" ^
        (List.nth_exn params.args 1) ^ ";\n");
     on_rez_nz
       (fun {args;tmp_gen;_} ->
          "{\n\
           assert map_vec_chain_coherent<" ^
          ityp ^ ">(?" ^
          (tmp_gen "cur_map") ^ ", ?" ^
          (tmp_gen "cur_vec") ^ ", " ^
          (tmp_gen "cur_ch") ^
          ");\n\
           mvc_coherent_alloc_is_halfowned<" ^ ityp ^
          ">(" ^
          (tmp_gen "cur_map") ^ ", " ^
          (tmp_gen "cur_vec") ^ ", " ^
          (tmp_gen "cur_ch") ^ ", *" ^
          (List.nth_exn args 1) ^ ");\n}");
   ];}

let dchain_rejuvenate_index_spec ityp =
  {ret_type = Static Sint32;
   arg_types = stt [Ptr dchain_struct; Sint32; vigor_time_t;];
   extra_ptr_types = [];
   lemmas_before = [
     capture_chain "cur_ch" 0;
     (fun {args;tmp_gen;_} ->
        "/*@ {\n\
         assert map_vec_chain_coherent<" ^
         ityp ^ ">(?" ^
        (tmp_gen "cur_map") ^ ", ?" ^
        (tmp_gen "cur_vec") ^ ", " ^
        (tmp_gen "cur_ch") ^
        ");\n\
         mvc_coherent_same_len(" ^
        (tmp_gen "cur_map") ^ ", " ^
        (tmp_gen "cur_vec") ^ ", " ^
        (tmp_gen "cur_ch") ^ ");\n} @*/");
     (fun {args;tmp_gen;_} ->
        "//@ rejuvenate_keeps_high_bounded(" ^
        (tmp_gen "cur_ch") ^
        ", " ^ (List.nth_exn args 1) ^
        ", " ^ (List.nth_exn args 2) ^
        ");\n");];
   lemmas_after = [
     (fun params ->
        "/*@ if (" ^ params.ret_name ^
        " != 0) { \n" ^
        "assert map_vec_chain_coherent<" ^ ityp ^ ">\
         (?cur_map,?cur_vec,?cur_ch);\n" ^
        "mvc_rejuvenate_preserves_coherent(cur_map,\
         cur_vec, cur_ch, " ^
        (List.nth_exn params.args 1) ^ ", "
        ^ (List.nth_exn params.args 2) ^
        ");\n\
         rejuvenate_preserves_index_range(cur_ch," ^
        (List.nth_exn params.args 1) ^ ", " ^
        (List.nth_exn params.args 2) ^ ");\n }@*/");
   ];}

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
