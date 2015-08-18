(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2015 - IMDEA Software Institute
 * Copyright (c) - 2012--2015 - Inria
 * 
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcModules
open EcFol
open EcEnv

open EcCoreGoal
open EcLowPhlGoal

module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
let to_args fun_ arg =
  match fun_.f_sig.fs_anames with
  | None     -> arg
  | Some [_] -> arg
  | Some lv  -> f_tuple (List.mapi (fun i v -> f_proj arg i v.v_type) lv)

(* -------------------------------------------------------------------- *)
let t_bdhoare_ppr_r tc =
  let env = FApi.tc1_env tc in
  let bhf = tc1_as_bdhoareF tc in
  let f_xpath = bhf.bhf_f in
  let fun_ = EcEnv.Fun.by_xpath f_xpath env in
  let penv,_qenv = EcEnv.Fun.hoareF_memenv f_xpath env in
  let m = EcIdent.create "&m" in
  let args = to_args fun_ (f_pvarg f_xpath fun_.f_sig.fs_arg m) in
  (* Warning: currently no substitution on pre,post since penv is always mhr *)
  let pre,post = bhf.bhf_pr, bhf.bhf_po in
  let fop = match bhf.bhf_cmp with
    | FHle -> f_real_le
    | FHge -> fun x y -> f_real_le y x
    | FHeq -> f_eq
  in
  let concl = fop (f_pr m f_xpath args post) bhf.bhf_bd in
  let concl = f_imp (Fsubst.f_subst_mem (fst penv) m pre) concl in
  let concl = f_forall_mems [m,snd penv] concl in
  FApi.xmutate1 tc `PPR [concl]

(* -------------------------------------------------------------------- *)
let t_hoare_ppr_r tc =
  ignore (tc1_as_hoareF tc);
  FApi.t_seq EcPhlCoreView.t_bdhoare_of_hoareF t_bdhoare_ppr_r tc

(* -------------------------------------------------------------------- *)
let t_equiv_ppr_r ty phi_l phi_r tc =
  let env = FApi.tc1_env tc in
  let ef = tc1_as_equivF tc in
  let (fl, fr) = (ef.ef_fl, ef.ef_fr) in
  let funl = EcEnv.Fun.by_xpath fl env in
  let funr = EcEnv.Fun.by_xpath fr env in
  let (penvl,penvr), (qenvl,qenvr) = EcEnv.Fun.equivF_memenv fl fr env in
  let argsl = to_args funl (f_pvarg fl funl.f_sig.fs_arg (fst penvl)) in
  let argsr = to_args funr (f_pvarg fr funr.f_sig.fs_arg (fst penvr)) in
  let a_id = EcIdent.create "a" in
  let a_f = f_local a_id ty in
  let smem1 = Fsubst.f_bind_mem Fsubst.f_subst_id mleft mhr in
  let smem2 = Fsubst.f_bind_mem Fsubst.f_subst_id mright mhr in
  let phi1 = Fsubst.f_subst smem1 phi_l in
  let phi2 = Fsubst.f_subst smem2 phi_r in
  let pr1 = f_pr (fst penvl) fl argsl (f_eq a_f phi1) in
  let pr2 = f_pr (fst penvr) fr argsr (f_eq a_f phi2) in
  let concl_pr =
    f_forall_mems [penvl; penvr]
      (f_forall_simpl [a_id,GTty ty]
         (f_imp_simpl ef.ef_pr (f_eq_simpl pr1 pr2))) in
  let concl_po =
    f_forall_mems [qenvl; qenvr]
      (f_forall_simpl [a_id, GTty ty]
         (f_imps_simpl [f_eq phi_l a_f;f_eq phi_r a_f] ef.ef_po)) in
  FApi.xmutate1 tc `PPR [concl_po; concl_pr]

(* -------------------------------------------------------------------- *)
let t_hoare_ppr   = FApi.t_low0 "hoare-ppr"   t_hoare_ppr_r
let t_bdhoare_ppr = FApi.t_low0 "bdhoare-ppr" t_bdhoare_ppr_r
let t_equiv_ppr   = FApi.t_low3 "equiv-ppr"   t_equiv_ppr_r

(* -------------------------------------------------------------------- *)
let process_ppr info tc =
  match info with
  | None ->
      t_hF_or_bhF_or_eF ~th:t_hoare_ppr ~tbh:t_bdhoare_ppr tc

  | Some (phi1, phi2) ->
      let hyps = FApi.tc1_hyps tc in
      let ef   = tc1_as_equivF tc in
      let qenv = snd (LDecl.equivF ef.ef_fl ef.ef_fr hyps) in
      let phi1 = TTC.pf_process_form_opt !!tc qenv None phi1 in
      let phi2 = TTC.pf_process_form_opt !!tc qenv None phi2 in
      if not (EcReduction.EqTest.for_type (LDecl.toenv qenv) phi1.f_ty phi2.f_ty) then
        tc_error !!tc "formulas must have convertible types";
      t_equiv_ppr phi1.f_ty phi1 phi2 tc

(* -------------------------------------------------------------------- *)
let t_prbounded_r conseq tc =
  let (env, _, concl) = FApi.tc1_eflat tc in

  let (m, pr, po, cmp, bd) =
    match concl.f_node with
    | FbdHoareF hf ->
        let m = fst (Fun.hoareF_memenv hf.bhf_f env) in
          (m, hf.bhf_pr, hf.bhf_po, hf.bhf_cmp, hf.bhf_bd)

    | FbdHoareS hf ->
        (hf.bhs_m, hf.bhs_pr, hf.bhs_po, hf.bhs_cmp, hf.bhs_bd)

    | _ -> tc_error_noXhl ~kinds:[`PHoare `Any] !!tc
  in

  let cond =
    (* FIXME: use the [conseq] result when possible *)
    match cmp with
    | FHle when f_equal bd f_r1 -> []
    | FHge when f_equal bd f_r0 -> []
    | _    when f_equal po f_false && f_equal bd f_r0 -> []
    | FHle when conseq -> [f_forall_mems [m] (f_imp pr (f_real_le f_r1 bd))]
    | FHge when conseq -> [f_forall_mems [m] (f_imp pr (f_real_le bd f_r0))]

    | _ -> tc_error !!tc "cannot solve the probabilistic judgement"
  in

  FApi.xmutate1 tc `PrBounded cond

let t_prbounded = FApi.t_low1 "pr-bounded" t_prbounded_r

(* -------------------------------------------------------------------- *)
let t_prfalse tc =
  let (env, _, concl) = FApi.tc1_eflat tc in

  let (f, ev, bd) =
    match concl.f_node with
    | Fapp ({f_node = Fop (op, _)}, [f; bd]) when is_pr f &&
          EcPath.p_equal op EcCoreLib.CI_Real.p_real_le
          || EcPath.p_equal op EcCoreLib.CI_Bool.p_eq->
        let pr = destr_pr f in (pr.pr_fun,pr.pr_event,bd)

      | Fapp ({f_node = Fop(op,_)}, [bd;f]) when is_pr f &&
          EcPath.p_equal op EcCoreLib.CI_Bool.p_eq->
        let pr = destr_pr f in (pr.pr_fun,pr.pr_event,bd)

      | _ -> tc_error !!tc "expecting a conclusion of the form Pr[...]"
  in

  (* the bound is zero *)
  let is_zero = f_real_le bd f_r0 in

  (* the event is false *)
  let smem  = Fsubst.f_bind_mem Fsubst.f_subst_id mhr mhr in
  let ev    = Fsubst.f_subst smem ev in
  let fun_  = EcEnv.Fun.by_xpath f env in
  let me    = EcEnv.Fun.actmem_post mhr f fun_ in
  let concl_po = f_forall_mems [me] (f_imp f_false ev) in

  FApi.xmutate1 tc `PrFalse [is_zero; concl_po]
