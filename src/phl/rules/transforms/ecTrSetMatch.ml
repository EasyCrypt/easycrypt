(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcAst
open EcTypes
open EcModules
open EcFol
open EcMatching
open EcPlTransform

module Zpr = EcMatching.Zipper

(* -------------------------------------------------------------------- *)
(* Parameters of the [set-match] transformation, resolved: the position is
   a normalized (possibly nested) code position, the pattern has been
   matched and its occurrences selected. *)
type tr_set_match = {
  trsm_at   : Position.nm_codepos;
  trsm_name : symbol;
  trsm_sub  : ss_inv;
  trsm_occ  : ptnpos;
}

type EcPlTransform.transform += TrSetMatch of tr_set_match

(* -------------------------------------------------------------------- *)
(* Assign the subterm to a fresh program variable just before the
   instruction, and replace its selected occurrences by that variable. *)
let set_match (p : tr_set_match) (ctxt : tr_ctxt) (s : stmt) =
  let zpr =
    try  Zpr.zipper_of_nm_cpos p.trsm_at s
    with Position.InvalidCPos ->
      raise (InvalidTransform "invalid code position") in

  let i, is =
    match zpr.Zpr.z_tail with
    | i :: is -> (i, is)
    | [] -> raise (InvalidTransform "invalid code position") in

  let e, mk =
    let e, kind, mk =
      get_expression_of_instruction i |> ofdfl (fun () ->
        raise (InvalidTransform
                 "targetted instruction should contain an expression")) in

    match kind with
    | `Sasgn | `Srnd | `Sif | `Smatch -> (e, mk)
    | `Swhile -> raise (InvalidTransform "while loops not supported")
  in

  let m    = fst ctxt.trc_me in
  let hyps = EcEnv.LDecl.init ctxt.trc_env [] in
  let e    = ss_inv_of_expr m e in
  let subf = EcSubst.ss_inv_rebind p.trsm_sub m in

  let v = { ov_name = Some p.trsm_name; ov_type = subf.inv.f_ty } in
  let (me, id) = EcMemory.bind_fresh v ctxt.trc_me in
  let pv = pv_loc (oget id.ov_name) in

  let occurrence pv t =
    if not (EcReduction.is_alpha_eq hyps subf.inv t) then
      raise (InvalidTransform "cannot find an occurrence of the pattern");
    pv in

  let e =
    try
      map_ss_inv2
        (fun pv -> FPosition.map p.trsm_occ (occurrence pv))
        (f_pvar pv subf.inv.f_ty m) e
    with InvalidPosition ->
      raise (InvalidTransform "cannot find an occurrence of the pattern") in

  let i1 = i_asgn (LvVar (pv, subf.inv.f_ty), expr_of_ss_inv subf) in
  let i2 = mk (expr_of_ss_inv e) in

  { trr_me  = me;
    trr_s   = Zpr.zip { zpr with Zpr.z_tail = i1 :: i2 :: is; };
    trr_obl = []; }

let () =
  register (function
    | TrSetMatch p -> Some (set_match p)
    | _ -> None)
