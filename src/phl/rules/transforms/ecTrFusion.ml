(* -------------------------------------------------------------------- *)
open EcUtils
open EcAst
open EcModules
open EcPlTransform

module Zpr = EcMatching.Zipper

(* -------------------------------------------------------------------- *)
(* Parameters of the [fusion] transformation, resolved: the position of
   the first loop is a normalized (possibly nested) code position. *)
type tr_fusion = {
  trfu_at   : EcMatching.Position.nm_codepos;
  trfu_init : int;
  trfu_d1   : int;
  trfu_d2   : int;
}

type EcPlTransform.transform += TrFusion of tr_fusion

(* -------------------------------------------------------------------- *)
(* Merge the loop at [p] with the next one, both headed by the same [n]
   instructions, their bodies ending with the same epilog after [d1] and
   [d2] instructions. *)
let fusion (p : tr_fusion) (ctxt : tr_ctxt) (s : stmt) =
  let env = ctxt.trc_env in
  let il, d1, d2 = p.trfu_init, p.trfu_d1, p.trfu_d2 in
  let error msg = raise (InvalidTransform msg) in

  let zpr =
    let cpos = EcMatching.Position.cpos_of_nm_cpos p.trfu_at in
    try  Zpr.zipper_of_cpos env cpos s
    with EcMatching.Position.InvalidCPos -> error "invalid code position" in

  let (hd, init1, b1, sw1, tl) =
    match zpr.Zpr.z_tail with
    | { i_node = Swhile (b, sw) } :: tl -> begin
        if List.length zpr.Zpr.z_head < il then
          error (Printf.sprintf
                   "1st while-loop is not headed by %d intruction(s)" il);
      let (init, hd) = List.takedrop il zpr.Zpr.z_head in
        (hd, init, b, sw, tl)
      end
    | _ -> error "code position does not lead to a while-loop"
  in

  let (init2, b2, sw2, tl) =
    if List.length tl < il then
      error (Printf.sprintf
               "1st first-loop is not followed by %d instruction(s)" il);
    let (init2, tl) = List.takedrop il tl in
      match tl with
      | { i_node = Swhile (b2, sw2) } :: tl -> (List.rev init2, b2, sw2, tl)
      | _ -> error "cannot find the 2nd while-loop"
  in

  if d1 > List.length sw1.s_node then
    error (Printf.sprintf
             "in loop-fusion, body is less than %d instruction(s)" d1);
  if d2 > List.length sw2.s_node then
    error (Printf.sprintf
             "in loop-fusion, body is less than %d instruction(s)" d2);

  let (sw1, fini1) = List.takedrop d1 sw1.s_node in
  let (sw2, fini2) = List.takedrop d2 sw2.s_node in

  (* FIXME: costly *)
  if not (EcReduction.EqTest.for_stmt env (stmt init1) (stmt init2)) then
    error "in loop-fusion, preludes do not match";
  if not (EcReduction.EqTest.for_stmt env (stmt fini1) (stmt fini2)) then
    error "in loop-fusion, epilogs do not match";
  if not (EcReduction.EqTest.for_expr env b1 b2) then
    error "in loop-fusion, while conditions do not match";

  EcTrFission.check_side_conditions ~exn:ctxt.trc_exn env b1 init1 sw1 sw2 fini1;

  let wl  = i_while (b1, stmt (sw1 @ sw2 @ fini1)) in
  let fus = List.rev_append init1 [wl] in

  { trr_me  = ctxt.trc_me;
    trr_s   = Zpr.zip { zpr with Zpr.z_head = hd; Zpr.z_tail = fus @ tl; };
    trr_obl = []; }

let () =
  register (function
    | TrFusion p -> Some (fusion p)
    | _ -> None)
