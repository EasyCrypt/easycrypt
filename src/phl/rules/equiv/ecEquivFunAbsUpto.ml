(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcTypes
open EcFol
open EcAst
open EcMemory
open EcModules
open EcEnv
open EcPV
open EcSubst

open EcCoreGoal
open EcLowPhlGoal

module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
(* Parameters of the equiv abstract-procedure upto rule, already typed.
   Nothing to resolve: the same record is the rule argument and the node
   payload. *)
type equiv_fun_abs_upto = {
  efu_ll   : bool;     (* lossless variant *)
  efu_bad  : ss_inv;   (* bad event B, read on the right *)
  efu_inv  : ts_inv;   (* invariant P, while B does not hold *)
  efu_binv : ts_inv;   (* invariant Q, once B holds *)
}

type EcCoreGoal.rule += REquivFunAbsUpto of equiv_fun_abs_upto

(* -------------------------------------------------------------------- *)
(* The pre- and postcondition of the conclusion of the rule, and its
   premises. *)
let equivF_abs_upto_spec (env : env) fl fr (r : equiv_fun_abs_upto) =
  let { efu_ll = weakened_pre; efu_bad = bad; efu_inv = invP; efu_binv = invQ } = r in

  let (topl, _fl, oil, sigl), (topr, _fr, oir, sigr) =
    EcLowPhlGoal.abstract_info2 env fl fr
  in

  let ml, mr = invP.ml, invP.mr in
  let bad = ss_inv_rebind bad invP.mr in
  let bad2 = ss_inv_generalize_left bad invP.ml in
  let allinv = map_ts_inv f_ands [bad2; invP; invQ] in
  let fvl = PV.fv env ml allinv.inv in
  let fvr = PV.fv env mr allinv.inv in

  PV.check_depend env fvl topl;
  PV.check_depend env fvr topr;

  (* FIXME: check there is only global variable *)
  let eqglob = ts_inv_eqglob topl ml topr mr in

  let ospec o_l o_r =
    EcPlFun.check_oracle_use env topl o_l;
    EcPlFun.check_oracle_use env topr o_r;

    let fo_l = EcEnv.Fun.by_xpath o_l env in
    let fo_r = EcEnv.Fun.by_xpath o_r env in
    let eq_params =
      ts_inv_eqparams
        fo_l.f_sig.fs_arg fo_l.f_sig.fs_anames ml
        fo_r.f_sig.fs_arg fo_r.f_sig.fs_anames mr in

    let eq_res =
      ts_inv_eqres fo_l.f_sig.fs_ret ml fo_r.f_sig.fs_ret mr in

    let pre   = map_ts_inv EcFol.f_ands [map_ts_inv1 EcFol.f_not bad2; eq_params; invP] in
    let post  = map_ts_inv3 EcFol.f_if_simpl bad2 invQ (map_ts_inv2 f_and eq_res invP) in
    let cond1 = f_equivF pre o_l o_r post in
    if not weakened_pre then
      let cond2 =
        let f_r1 = {m=invQ.ml; inv=f_r1} in
        let concl = ts_inv_lower_left1 (fun bq -> (f_bdHoareF bq o_l bq FHeq f_r1)) invQ in
        f_forall_mems_ss_inv (mr, abstract_mt)
          (map_ss_inv2 f_imp bad concl) in
      let cond3 =
        let f_r1 = {m=invQ.mr; inv=f_r1} in
        let bq = map_ts_inv2 f_and bad2 invQ in
          f_forall_mems_ss_inv (ml, abstract_mt) (ts_inv_lower_right1 (fun bq -> f_bdHoareF bq o_r bq FHeq f_r1) bq) in

      [cond1; cond2; cond3]
    else
      let cond2 =
        let concl = ts_inv_lower_left1 (fun bq -> (f_hoareF bq o_l (POE.lift bq))) invQ in
        f_forall_mems_ss_inv (mr, abstract_mt)
          (map_ss_inv2 f_imp bad concl) in
      let cond3 =
        let bq = map_ts_inv2 f_and bad2 invQ in
          f_forall_mems_ss_inv (ml, abstract_mt) (ts_inv_lower_right1 (fun bq -> f_hoareF bq o_r (POE.lift bq)) bq) in

      [cond1; cond2; cond3]
  in

  let sg = List.map2 ospec (OI.allowed oil) (OI.allowed oir) in
  let sg = List.flatten sg in
  let lossless_a = if not weakened_pre then
     [ EcPlFun.lossless_hyps env topl fl.x_sub ]
  else
    [ f_losslessF fl; f_losslessF fr ]
  in
  let sg = lossless_a @ sg in

  let eq_params =
    ts_inv_eqparams
      sigl.fs_arg sigl.fs_anames ml
      sigr.fs_arg sigr.fs_anames mr in

  let eq_res = ts_inv_eqres sigl.fs_ret ml sigr.fs_ret mr in

  let pre  = [eqglob;invP] in
  let pre  = map_ts_inv3 f_if_simpl bad2 invQ (map_ts_inv f_ands (eq_params::pre)) in
  let post = map_ts_inv3 f_if_simpl bad2 invQ (map_ts_inv f_ands [eq_res;eqglob;invP]) in

  (pre, post, sg)

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. Its side conditions (the
   procedures are instances of the same abstract procedure, the formulas
   do not depend on its globals, the oracles do not access them, the goal
   is the conclusion of the rule) are part of it, so the checker
   re-validates them. *)
let equivF_abs_upto_subgoals
    (hyps : LDecl.hyps) (ef : equivF) (n : equiv_fun_abs_upto)
=
  let pre, post, sg =
    equivF_abs_upto_spec (LDecl.toenv hyps) ef.ef_fl ef.ef_fr n in
  if not (   EcReduction.ts_inv_alpha_eq hyps (ef_pr ef) pre
          && EcReduction.ts_inv_alpha_eq hyps (ef_po ef) post) then
    failwith "equivF-fun-abs-upto: the judgement is not the conclusion of the rule";
  sg

(* -------------------------------------------------------------------- *)
(* Rule (TCB). *)
let t_equivF_abs_upto (r : equiv_fun_abs_upto) (tc : tcenv1) =
  let ef = tc1_as_equivF tc in
  FApi.xrule1 tc (REquivFunAbsUpto r)
    (equivF_abs_upto_subgoals (FApi.tc1_hyps tc) ef r)

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | REquivFunAbsUpto n ->
         Some (EcPlRecheck.checker_of "equivF-fun-abs-upto" pf_as_equivF
                 (fun hyps ef -> equivF_abs_upto_subgoals hyps ef n))
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node): the consequence to the conclusion of the rule,
   then the rule.

   TEMPORARY: the consequence rule still comes from the not-yet-migrated
   [EcPhlConseq]. *)
let t_equivF_abs_upto_full (r : equiv_fun_abs_upto) (tc : tcenv1) =
  let env = FApi.tc1_env tc in
  let ef  = tc1_as_equivF tc in
  let pre, post, _ = equivF_abs_upto_spec env ef.ef_fl ef.ef_fr r in
  FApi.t_last (t_equivF_abs_upto r) (EcPhlConseq.t_equivF_conseq pre post tc)

(* -------------------------------------------------------------------- *)
(* Elaboration. *)
let process_equivF_abs_upto_info (info : fun_upto_info) (tc : tcenv1) =
  let hyps = FApi.tc1_hyps tc in
  let ml, mr = (EcIdent.create "&1", EcIdent.create "&2") in
  let env' = LDecl.inv_memenv ml mr hyps in
  let p = TTC.pf_process_form !!tc env' tbool info.fui_pre in
  let q = info.fui_pos |> omap (TTC.pf_process_form !!tc env' tbool) |> odfl f_true in
  let m = EcIdent.create "&hr" in
  let bad =
    let env' = LDecl.push_active_ss (EcMemory.abstract m) hyps in
    TTC.pf_process_form !!tc env' tbool info.fui_bad
  in
  { efu_ll   = odfl false info.fui_is_ll_variant;
    efu_bad  = { inv = bad; m };
    efu_inv  = { inv = p; ml; mr };
    efu_binv = { inv = q; ml; mr }; }

let process_equivF_abs_upto (info : fun_upto_info) (tc : tcenv1) =
  t_equivF_abs_upto_full (process_equivF_abs_upto_info info tc) tc
