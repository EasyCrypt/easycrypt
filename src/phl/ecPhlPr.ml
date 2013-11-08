(* -------------------------------------------------------------------- *)
open EcUtils
open EcTypes
open EcModules
open EcFol
open EcEnv
open EcBaseLogic
open EcLogic
open EcCorePhl
open EcCoreHiLogic
open EcCoreHiPhl

(* -------------------------------------------------------------------- *)
let t_ppr ty phi_l phi_r g =
  let env,_,concl = get_goal_e g in
  let ef = t_as_equivF concl in
  let fl,fr = ef.ef_fl,ef.ef_fr in

  let funl = EcEnv.Fun.by_xpath fl env in
  let funr = EcEnv.Fun.by_xpath fr env in
  let paramsl = funl.f_sig.fs_params in
  let paramsr = funr.f_sig.fs_params in
  let (penvl,penvr), (qenvl,qenvr) = EcEnv.Fun.equivF_memenv fl fr env in
  let argsl = List.map (fun v -> f_pvloc fl v (fst penvl)) paramsl in
  let argsr = List.map (fun v -> f_pvloc fr v (fst penvr)) paramsr in
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
  prove_goal_by [concl_po;concl_pr] (RN_xtd (new EcPhlDeno.rn_hl_deno)) g

(* -------------------------------------------------------------------- *)
let process_equiv_ppr (phi1,phi2) g =
  let hyps,concl = get_goal g in
  let ef = t_as_equivF concl in
  let _penv,qenv = LDecl.equivF ef.ef_fl ef.ef_fr hyps in
  let phi1 = process_form_opt qenv phi1 None in
  let phi2 = process_form_opt qenv phi2 None in
  (* TODO: check for type unification *)
  let ty = f_ty phi1 in
    t_ppr ty phi1 phi2 g

let process_bdhoare_ppr g =
  let env,_,concl = get_goal_e g in
  let bhf = 
    try t_as_bdHoareF concl 
    with _ -> 
      tacuerror "Only bounded-hoare over functions are supported."
  in
  let f_xpath = bhf.bhf_f in
  let fun_ = EcEnv.Fun.by_xpath f_xpath env in
  let params = fun_.f_sig.fs_params in
  let penv,_qenv = EcEnv.Fun.hoareF_memenv f_xpath env in
  let args = List.map (fun v -> f_pvloc f_xpath v (fst penv)) params in
  (* Warning: currently no substitution on pre,post since penv is always mhr *)
  let pre,post = bhf.bhf_pr, bhf.bhf_po in
  let fop = match bhf.bhf_cmp with
    | FHle -> f_real_le 
    | FHge -> fun x y -> f_real_le y x 
    | FHeq -> f_eq 
  in
  let m = EcIdent.create "&m" in
  let concl = f_imp (Fsubst.f_subst_mem (fst penv) m pre) (fop (f_pr m f_xpath args post) bhf.bhf_bd) in
  let concl = f_forall_mems [m,None] concl in
  prove_goal_by [concl] (RN_xtd (new EcPhlDeno.rn_hl_deno)) g

let process_ppr info g =
  match info with
    | Some (phi1,phi2) -> process_equiv_ppr (phi1,phi2) g
    | None -> process_bdhoare_ppr g



(* -------------------------------------------------------------------- *)
class rn_hl_prbounded =
object
  inherit xrule "[hl] pr-bounded"
end

let rn_hl_prbounded =
  RN_xtd (new rn_hl_prbounded)

(* -------------------------------------------------------------------- *)
let t_prbounded conseq g = 
  let env, _, concl = get_goal_e g in
  let m, pr, po, cmp, bd = 
    match concl.f_node with
    | FbdHoareF hf ->
      let m, _ = Fun.hoareF_memenv hf.bhf_f env in
      m, hf.bhf_pr, hf.bhf_po, hf.bhf_cmp, hf.bhf_bd 
    | FbdHoareS hf -> hf.bhs_m, hf.bhs_pr, hf.bhs_po, hf.bhs_cmp, hf.bhs_bd
    | _ -> tacuerror "bd_hoare excepted" in
  let cond = 
    match cmp with
    | FHle when f_equal bd f_r1 -> []
    | FHge when f_equal bd f_r0 -> []
    | _ when f_equal po f_false && f_equal bd f_r0 -> []
    (* TODO use the conseq rule instead *)
    | FHle when conseq -> [f_forall_mems [m] (f_imp pr (f_real_le f_r1 bd))]
    | FHge when conseq -> [f_forall_mems [m] (f_imp pr (f_real_le bd f_r0))]
    | _ -> cannot_apply "pr_bounded" "cannot solve the probabilistic judgement" in
  prove_goal_by cond rn_hl_prbounded g

(* -------------------------------------------------------------------- *)
(* FIXME: can be replaced by rewrite_pr *)
class rn_hl_prfalse =
object
  inherit xrule "[hl] pr-false"
end

let rn_hl_prfalse =
  RN_xtd (new rn_hl_prfalse)

(* -------------------------------------------------------------------- *)
let t_prfalse g = 
  let env,_, concl = get_goal_e g in
  let f,ev,bd =
    match concl.f_node with
      | Fapp ({f_node = Fop(op,_)}, [f;bd]) when is_pr f &&
          EcPath.p_equal op EcCoreLib.p_real_le
          || EcPath.p_equal op EcCoreLib.p_eq->
        let (_m,f,_args,ev) = destr_pr f in
        f,ev,bd
      | Fapp ({f_node = Fop(op,_)}, [bd;f]) when is_pr f &&
          EcPath.p_equal op EcCoreLib.p_eq->
        let (_m,f,_args,ev) = destr_pr f in
        f,ev,bd
      | _ ->
        cannot_apply "pr_false" "Pr[..] expression was expected"
  in
  (* the bound is zero *)
  let is_zero = f_real_le bd f_r0 in

  (* the event is false *)
  let smem_ = Fsubst.f_bind_mem Fsubst.f_subst_id mhr mhr in 
  let ev   = Fsubst.f_subst smem_ ev in
  let fun_ = EcEnv.Fun.by_xpath f env in
  let me = EcEnv.Fun.actmem_post mhr f fun_ in
  let concl_po = f_forall_mems [me] (f_imp f_false ev) in
    prove_goal_by [is_zero;concl_po] rn_hl_prfalse g
