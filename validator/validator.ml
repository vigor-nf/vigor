open Core.Std
open Ir

let validate_prefix fin fout intermediate_pref verifast_bin proj_root =
  let spec_mod =  match !Fspec_api.spec with
    | Some m -> m
    | None -> failwith "Failed: could not find function spec dynamic module"
  in
  let module Spec = (val spec_mod) in
  let assumptions_fname = intermediate_pref ^ ".assumptions.vf" in
  let lino_fname = intermediate_pref ^ ".lino.int" in
  let export_out_fname = intermediate_pref ^ ".export.stdout" in
  let verify_out_fname = intermediate_pref ^ ".verify.stdout" in
  let ir_fname = intermediate_pref ^ ".ir" in
  let intermediate_fout = intermediate_pref ^ ".tmp.c" in
  let ir = Import.build_ir Spec.fun_types fin Spec.preamble Spec.boundary_fun Spec.finishing_fun in
  Out_channel.write_all ir_fname ~data:(Sexp.to_string (sexp_of_ir ir));
  Render.render_ir ir intermediate_fout;
  match Verifier.verify_file
          verifast_bin intermediate_fout verify_out_fname proj_root
  with
  | Verifier.Valid ->
    ignore (Sys.command ("cp " ^ intermediate_fout ^ " " ^ fout));
    printf "Valid.\n"
  | Verifier.Invalid _ ->
    begin
      let vf_assumptions = Verifier.export_assumptions
          verifast_bin intermediate_fout ir.export_point
          assumptions_fname lino_fname export_out_fname
          proj_root
      in
      let justified = Analysis.induce_symbolic_assignments
          Spec.fixpoints ir vf_assumptions
      in
      if justified then
        printf "\\/alid.\n"
      else
        printf "Failed.\n"
      (* Render.render_ir ir fout; *)
      (* match Verifier.verify_file *)
      (*         verifast_bin fout verify_out_fname proj_root *)
      (* with *)
      (* | Verifier.Valid -> printf "\\/alid.\n" *)
      (* | Verifier.Invalid cause -> printf "Failed: %s\n" cause *)
    end

let load_plug fname =
  let fname = Dynlink.adapt_filename fname in
  match Sys.file_exists fname with
  | `No | `Unknown -> failwith ("Plugin file " ^ fname ^ " does not exist")
  | `Yes -> begin
      try Dynlink.loadfile fname
      with
      | (Dynlink.Error err) as e ->
        print_endline ("ERROR loading plugin: " ^ (Dynlink.error_message err) );
        raise e
      | _ -> failwith "Unknow error while loading plugin"
    end

let () =
  load_plug Sys.argv.(1);
  validate_prefix Sys.argv.(2) Sys.argv.(3) Sys.argv.(4) Sys.argv.(5) Sys.argv.(6)
