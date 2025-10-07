(* -------------------------------------------------------------------- *)
open EcUtils
open EcModules
open EcFol
open EcEnv
open EcAst
open EcCoreGoal
open EcLowPhlGoal
open EcSubst

module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
let to_args fun_ arg =
  match fun_.f_sig.fs_anames with
  | []  -> f_tt
  | [_] -> arg
  | lv  -> f_tuple (List.mapi (fun i v -> f_proj arg i v.ov_type) lv)

(* -------------------------------------------------------------------- *)
let t_bdhoare_ppr_r tc =
  let env = FApi.tc1_env tc in
  let bhf = tc1_as_bdhoareF tc in
  let f_xpath = bhf.bhf_f in
  let fun_ = EcEnv.Fun.by_xpath f_xpath env in
  let penv,_qenv = EcEnv.Fun.hoareF_memenv bhf.bhf_m f_xpath env in
  let m = EcIdent.create "&hr" in
  let args = map_ss_inv1 (to_args fun_) (f_pvarg fun_.f_sig.fs_arg m) in
  let pre,post = (bhf_pr bhf), (bhf_po bhf) in
  let fop = match bhf.bhf_cmp with
    | FHle -> f_real_le
    | FHge -> fun x y -> f_real_le y x
    | FHeq -> f_eq
  in
  let bd = ss_inv_rebind (bhf_bd bhf) m in
  let concl = map_ss_inv2 fop (map_ss_inv1 (fun args -> f_pr m f_xpath args post) args)
    bd in
  let pre   = ss_inv_rebind pre m in
  let concl = map_ss_inv2 f_imp pre concl in
  let concl = EcSubst.f_forall_mems_ss_inv (m,snd penv) concl in
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
  let (penvl,penvr), (qenvl,qenvr) = EcEnv.Fun.equivF_memenv ef.ef_ml ef.ef_mr fl fr env in
  let m = EcIdent.create "&hr" in
  let argsl = map_ss_inv1 (to_args funl) (f_pvarg funl.f_sig.fs_arg (fst penvl)) in
  let argsr = map_ss_inv1 (to_args funr) (f_pvarg funr.f_sig.fs_arg (fst penvr)) in
  let a_id = EcIdent.create "a" in
  let a_f = f_local a_id ty in
  let pr1_ev = EcSubst.ss_inv_rebind (map_ss_inv1 (fun p -> f_eq p a_f) phi_l) m in
  let pr1 = f_pr (fst penvl) fl argsl.inv pr1_ev in
  let pr2_ev = EcSubst.ss_inv_rebind (map_ss_inv1 (fun p -> f_eq p a_f) phi_r) m in
  let pr2 = f_pr (fst penvr) fr argsr.inv pr2_ev in
  let concl_pr =
    f_forall_mems_ts_inv penvl penvr
      (map_ts_inv1 (f_forall_simpl [a_id,GTty ty])
         (map_ts_inv1 (fun pr -> f_imp_simpl pr (f_eq_simpl pr1 pr2)) (ef_pr ef))) in
  let phi_l = ss_inv_generalize_as_left phi_l ef.ef_ml ef.ef_mr in
  let phi_r = ss_inv_generalize_as_right phi_r ef.ef_ml ef.ef_mr in
  let concl_po = f_forall_mems_ts_inv qenvl qenvr (map_ts_inv3 (fun phi_l phi_r po ->
      (f_forall_simpl [a_id, GTty ty]
         (f_imps_simpl [f_eq phi_l a_f;f_eq phi_r a_f] po))) phi_l phi_r (ef_po ef)) in
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
      let qenvl = snd (LDecl.hoareF ef.ef_ml ef.ef_fl hyps) in
      let qenvr = snd (LDecl.hoareF ef.ef_mr ef.ef_fr hyps) in
      let phi1 = TTC.pf_process_form_opt !!tc qenvl None phi1 in 
      let phi2 = TTC.pf_process_form_opt !!tc qenvr None phi2 in
      if not (EcReduction.EqTest.for_type (LDecl.toenv hyps) phi1.f_ty phi2.f_ty) then
        tc_error !!tc "formulas must have convertible types";
      t_equiv_ppr phi1.f_ty {m=ef.ef_ml;inv=phi1} {m=ef.ef_mr;inv=phi2} tc

(* -------------------------------------------------------------------- *)
let t_prbounded_r conseq tc =
  let (env, _, concl) = FApi.tc1_eflat tc in

  let (m, pr, po, cmp, bd) =
    match concl.f_node with
    | FbdHoareF hf ->
        let m = fst (Fun.hoareF_memenv hf.bhf_m hf.bhf_f env) in
          (m, bhf_pr hf, bhf_po hf, hf.bhf_cmp, bhf_bd hf)

    | FbdHoareS hf ->
        (hf.bhs_m, bhs_pr hf, bhs_po hf, hf.bhs_cmp, bhs_bd hf)

    | _ -> tc_error_noXhl ~kinds:[`PHoare `Any] !!tc
  in

  let cond =
    (* FIXME: use the [conseq] result when possible *)
    match cmp with
    | FHle when f_equal bd.inv f_r1 -> []
    | FHge when f_equal bd.inv f_r0 -> []
    | _    when f_equal po.inv f_false && f_equal bd.inv f_r0 -> []
    | FHle when conseq -> [f_forall_mems_ss_inv m (map_ss_inv2 f_imp pr (map_ss_inv2 f_real_le {m=fst m;inv=f_r1} bd))]
    | FHge when conseq -> [f_forall_mems_ss_inv m (map_ss_inv2 f_imp pr (map_ss_inv2 f_real_le bd {m=fst m;inv=f_r0}))]

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
  let smem  = Fsubst.f_bind_mem Fsubst.f_subst_id ev.m ev.m in
  let ev'    = Fsubst.f_subst smem ev.inv in
  let fun_  = EcEnv.Fun.by_xpath f env in
  let me    = EcEnv.Fun.actmem_post ev.m fun_ in
  let concl_po = f_forall_mems [me] (f_imp f_false ev') in

  FApi.xmutate1 tc `PrFalse [is_zero; concl_po]
