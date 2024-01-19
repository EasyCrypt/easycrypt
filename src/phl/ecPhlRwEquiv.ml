open EcUtils
open EcLocation
open EcParsetree
open EcFol
open EcModules
open EcPath

open EcCoreGoal
open EcCoreGoal.FApi
open EcLowGoal
open EcLowPhlGoal

(*---------------------------------------------------------------------------------------*)
type rwe_error =
  | RWE_InvalidFunction of xpath * xpath
  | RWE_InvalidPosition

exception RwEquivError of rwe_error

let rwe_error e = raise (RwEquivError e)

(*---------------------------------------------------------------------------------------*)
(*
  `rewrite equiv` - replace a call to a procedure with an equivalent call, using an equiv

  Arguments,
    side: selects the program we are rewriting in
    dir: selects the direction in which the equiv will be applied
    cp: selects the position of the call that is being targetted
    equiv, equiv_pt: the equiv and it's corresponding proof term to use for rewriting
    rargslv: an optional argument list and left-value that can be used for instances
             when the procedure being rewritten to requires a different set of arguments
             and return value.
*)
(* FIXME: What is a good interface for this tactic? *)
let t_rewrite_equiv side dir cp (equiv : equivF) equiv_pt rargslv tc =
  let env = tc1_env tc in
  let goal = tc1_as_equivS tc in

  let code =
    match side with
    | `Left  -> goal.es_sl
    | `Right -> goal.es_sr
  in

  (* FIXME: can we just take in the proof term for the equiv? *)
  (* If not we need some validation that the proof term is useful *)

  (* Extract the correct functions from the equiv *)
  let new_func, old_func =
    match dir with
    | `LtoR -> equiv.ef_fr, equiv.ef_fl
    | `RtoL -> equiv.ef_fl, equiv.ef_fr
  in

  (* Extract the call statement and surrounding code *)
  let prefix, (llv, func, largs), suffix =
    let p, i, s = s_split_i cp code in
    if not (is_call i) then
      rwe_error RWE_InvalidPosition;
    stmt p, destr_call i, stmt s
  in

  (* Make sure the function call matches the equiv target *)
  if not (EcEnv.NormMp.x_equal env old_func func) then
    rwe_error (RWE_InvalidFunction (func, old_func));

  (* Construct the new program that we want *)
  let rargs, rlv = odfl (largs, llv) rargslv in
  let prog = s_call (rlv, new_func, rargs) in
  let prog = s_seq prefix (s_seq prog suffix) in

  let tc = EcPhlOutline.t_equivS_trans_eq side prog tc in

  (* One of the goals can be simplified, often fully, using the provided equiv *)
  let tp = match side with | `Left -> 1 | `Right -> 2 in
  let p = EcHiGoal.process_tfocus tc (Some [Some tp, Some tp], None) in
  t_onselect
    p
    (t_seqs [
      EcPhlEqobs.process_eqobs_in none {sim_pos = some (cp, cp); sim_hint = ([], none); sim_eqs = none};
      (match side, dir with
       | `Left, `LtoR  -> t_id
       | `Left, `RtoL  -> EcPhlSym.t_equiv_sym
       | `Right, `LtoR -> EcPhlSym.t_equiv_sym
       | `Right, `RtoL  -> t_id);
      EcPhlCall.t_call None (f_equivF_r equiv);
      t_try (t_apply equiv_pt); (* FIXME: Can do better here, we know this applies to just the first sub goal of call *)
      t_try (t_seqs [
        EcPhlInline.process_inline (`ByName (None, None, ([], None)));
        EcPhlAuto.t_auto;
        EcHiGoal.process_done;
      ]);
    ])
    tc

(*---------------------------------------------------------------------------------------*)
(* Proccess a user call to rewrite equiv *)

let process_rewrite_equiv info tc =
  let side = info.rw_eqv_side in
  let cp = info.rw_eqv_pos in
  let dir = info.rw_eqv_dir in
  let lem_pt = info.rw_eqv_lemma in

  (* Process the lemma proof term *)
  let equiv, eqv_pt =
    try
      let lem_pt = EcProofTerm.tc1_process_full_pterm tc lem_pt in
      let lem_pt, lem_f = EcProofTerm.concretize lem_pt in
      EcFol.destr_equivF lem_f, lem_pt
    with DestrError _ ->
      tc_error !!tc "rewrite equiv: provided lemma is not an equiv"
  in

  (* Get the xpath of the target function *)
  let new_func =
    match dir with
    | `LtoR -> equiv.ef_fr
    | `RtoL -> equiv.ef_fl
  in

  let env = tc1_env tc in
  let goal = tc1_as_equivS tc in

  (* Check which memory we are using for the arguments *)
  let mem =
    match side with
    | `Left  -> goal.es_ml
    | `Right -> goal.es_mr
  in

  (* Translate any pexprs if present *)
  let rargslv =
    match info.rw_eqv_proc with
    | None -> None
    | Some (pargs, pres) ->
        begin
          try
            let proc = EcEnv.Fun.by_xpath new_func env in
            let subenv = EcEnv.Memory.push_active mem env in
            let ue = EcUnify.UniEnv.create (Some []) in
            let args, ret_ty = EcTyping.trans_args subenv ue (loc pargs) proc.f_sig (unloc pargs) in
            let res = omap (fun v -> EcTyping.transexpcast subenv `InProc ue ret_ty v) pres in
            let es = e_subst (Tuni.subst (EcUnify.UniEnv.close ue)) in
            Some (List.map es args, omap (EcModules.lv_of_expr |- es) res)
          with EcUnify.UninstanciateUni ->
            EcTyping.tyerror (loc pargs) env EcTyping.FreeTypeVariables
        end
  in

  (* Offload to the tactic *)
  try
    t_rewrite_equiv side dir cp equiv eqv_pt rargslv tc
  with
  | RwEquivError (RWE_InvalidFunction (got, wanted)) ->
      tc_error !!tc "rewrite equiv: function mismatch\nExpected %s but got %s" (x_tostring wanted) (x_tostring got)
  | RwEquivError RWE_InvalidPosition ->
      tc_error !!tc "rewrite equiv: targetted instruction is not a function call"

