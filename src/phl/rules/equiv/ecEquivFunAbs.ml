(* -------------------------------------------------------------------- *)
open EcParsetree
open EcTypes
open EcFol
open EcAst
open EcModules
open EcEnv
open EcPV

open EcCoreGoal
open EcLowPhlGoal

module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
(* Parameter of the equiv abstract-procedure rule: the invariant, already
   typed. Nothing to resolve: the same record is the rule argument and the
   node payload. *)
type equiv_fun_abs = {
  efa_inv : ts_inv;   (* relational invariant I *)
}

type EcCoreGoal.rule += REquivFunAbs of equiv_fun_abs

(* -------------------------------------------------------------------- *)
let equivF_abs_spec (env : env) fl fr (inv : ts_inv) =
  let (topl, _fl, oil, sigl), (topr, _fr, oir, sigr) =
    EcLowPhlGoal.abstract_info2 env fl fr
  in

  let ml, mr = inv.ml, inv.mr in
  let fvl = PV.fv env inv.ml inv.inv in
  let fvr = PV.fv env inv.mr inv.inv in
  PV.check_depend env fvl topl;
  PV.check_depend env fvr topr;
  let eqglob = ts_inv_eqglob topl ml topr mr in

  let ospec o_l o_r =
    let use =
      try
        EcPlFun.check_oracle_use env topl o_l;
        EcPlFun.check_oracle_use env topr o_r;
        false
      with _ -> true
    in

    let fo_l = EcEnv.Fun.by_xpath o_l env in
    let fo_r = EcEnv.Fun.by_xpath o_r env in

    let eq_params =
      f_eqparams
        fo_l.f_sig.fs_arg fo_l.f_sig.fs_anames ml
        fo_r.f_sig.fs_arg fo_r.f_sig.fs_anames mr in

    let eq_res =
      f_eqres fo_l.f_sig.fs_ret ml fo_r.f_sig.fs_ret mr in

    let invs = if use then [eqglob; inv] else [inv] in
    let pre  = map_ts_inv (fun invs -> EcFol.f_ands (eq_params :: invs)) invs in
    let post = map_ts_inv (fun invs -> EcFol.f_ands (eq_res :: invs)) invs in
    f_equivF pre o_l o_r post
  in

  let sg = List.map2 ospec (OI.allowed oil) (OI.allowed oir) in

  let eq_params =
    f_eqparams
      sigl.fs_arg sigl.fs_anames ml
      sigr.fs_arg sigr.fs_anames mr in

  let eq_res = ts_inv_eqres sigl.fs_ret ml sigr.fs_ret mr in
  let lpre   = [eqglob;inv] in
  let pre    = map_ts_inv (fun lpre -> f_ands (eq_params::lpre)) lpre in
  let post   = map_ts_inv f_ands [eq_res; eqglob; inv] in

  (pre, post, sg)

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. Its side conditions (the
   procedures are instances of the same abstract procedure, the invariant
   does not depend on its globals, the goal is the conclusion of the rule)
   are part of it, so the checker re-validates them. *)
let equivF_abs_subgoals (hyps : LDecl.hyps) (ef : equivF) (n : equiv_fun_abs) =
  let pre, post, sg =
    equivF_abs_spec (LDecl.toenv hyps) ef.ef_fl ef.ef_fr n.efa_inv in
  if not (   EcReduction.ts_inv_alpha_eq hyps (ef_pr ef) pre
          && EcReduction.ts_inv_alpha_eq hyps (ef_po ef) post) then
    failwith "equivF-fun-abs: the judgement is not the conclusion of the rule";
  sg

(* -------------------------------------------------------------------- *)
(* Rule (TCB). *)
let t_equivF_abs (r : equiv_fun_abs) (tc : tcenv1) =
  let ef = tc1_as_equivF tc in
  FApi.xrule1 tc (REquivFunAbs r) (equivF_abs_subgoals (FApi.tc1_hyps tc) ef r)

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | REquivFunAbs n ->
         Some (EcPlRecheck.checker_of "equivF-fun-abs" pf_as_equivF
                 (fun hyps ef -> equivF_abs_subgoals hyps ef n))
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node): the consequence to the conclusion of the rule,
   then the rule.

   TEMPORARY: the consequence rule still comes from the not-yet-migrated
   [EcPhlConseq]. *)
let t_equivF_abs_full (r : equiv_fun_abs) (tc : tcenv1) =
  let env = FApi.tc1_env tc in
  let ef  = tc1_as_equivF tc in
  let pre, post, _ = equivF_abs_spec env ef.ef_fl ef.ef_fr r.efa_inv in
  FApi.t_last (t_equivF_abs r) (EcPhlConseq.t_equivF_conseq pre post tc)

(* -------------------------------------------------------------------- *)
(* Elaboration: the goal is known to be an [equivF]. *)
let process_equivF_abs (inv : pformula) (tc : tcenv1) =
  let hyps   = FApi.tc1_hyps tc in
  let ml, mr = EcIdent.create "&1", EcIdent.create "&2" in
  let env'   = LDecl.inv_memenv ml mr hyps in
  let inv    = TTC.pf_process_form !!tc env' tbool inv in
  t_equivF_abs_full { efa_inv = { inv; ml; mr; } } tc
