open Core

type verification_outcome =
  | Valid
  | Inconsistent
  | Invalid_seq
  | Invalid_rez of string

let verify_ir ir verifast fname outf proj_root lino_fname =
  Render.render_ir ir fname ~render_assertions:true;
  let _ = Sys.command (verifast ^ " -c -prover z3v4.5 -I " ^ proj_root ^
                       " -I ../libvig/models/dpdk" ^
                       " " ^ fname ^ " > " ^ outf)
  in
  let vf_succeded = Sys.command ("grep '0 errors found' " ^ outf ^
                                 " > /dev/null")
  in
  if vf_succeded = 0 then Valid
  else
    let unproven_assertion =
      Sys.command ("grep 'Assertion might not hold' " ^ outf ^ " > /dev/null")
    in
    let err = In_channel.read_all outf in
    if unproven_assertion = 0 then Invalid_rez "Can not prove assertion"
    else Invalid_rez err
(* TODO: this is more thorough version, that checks separately for bugs in the
   call prefix preceding the tip call; and insonsistency (i.e. the incompatible
   assumptions). It helps to spot symbex overapproximations, incorrect symbex
   models, broken lemmas, contracts etc. However it slows down validation by a
   factor of 3, which has became unbearable with the huge amount of VigLB
   traces.*)
  (* let vf_succeded = Sys.command ("grep '0 errors found' " ^ outf ^
   *                                " > /dev/null")
   * in
   * let _ = Sys.command (verifast ^ " -c -prover z3v4.5 -I " ^ proj_root ^
   *                      " -I ../libvig/models/dpdk" ^
   *                      " " ^ fname ^ " > " ^ outf)
   * in
   * if vf_succeded <> 0 then Invalid_seq
   * else begin
   *   Render.render_ir ir fname ~render_assertions:true;
   *   let _ = Sys.command (verifast ^ " -c -prover z3v4.5 -I " ^
   *                        proj_root ^ " -I ../libvig/models/dpdk" ^
   *                        " " ^ fname ^ " > " ^ outf)
   *   in
   *   let vf_succeded = Sys.command ("grep '0 errors found' " ^ outf ^
   *                                  " > /dev/null") in
   *   if vf_succeded = 0 then begin
   *     let _ = (\* locate the line to dump VeriFast assumptions *\)
   *       Sys.command ("sed -n '/" ^ ir.Ir.export_point ^ "/=' " ^
   *                    fname ^ " > " ^ lino_fname)
   *     in
   *     let export_lino = String.strip (In_channel.read_all lino_fname) in
   *     let _ = Sys.command (verifast ^ " -c -prover z3v4.5 -I " ^ proj_root ^
   *                          " -I ../libvig/models/dpdk" ^
   *                          " -breakpoint " ^ export_lino ^
   *                          " " ^ fname ^ " > " ^ outf)
   *     in
   *     let consistent = Sys.command ("grep 'Breakpoint reached' " ^ outf ^
   *                                   " > /dev/null")
   *     in
   *     if consistent = 0 then Valid
   *     else Inconsistent
   *   end
   *   else begin
   *     let unproven_assertion =
   *       Sys.command ("grep 'Assertion might not hold' " ^
   *                    outf ^ " > /dev/null")
   *     in
   *     let err = In_channel.read_all outf in
   *     if unproven_assertion = 0 then Invalid_rez "Can not prove assertion"
   *     else Invalid_rez err
   *   end
   * end *)
