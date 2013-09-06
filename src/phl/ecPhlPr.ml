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
  let mk_local v =
    let v_id = EcIdent.create v.v_name in
    (v_id,v.v_type),f_local v_id v.v_type
  in
  let argsl = List.map mk_local paramsl in
  let argsr = List.map mk_local paramsr in

  let m1_id = EcIdent.create "&m1" in
  let m2_id = EcIdent.create "&m2" in
  let a_id = EcIdent.create "a" in
  let a_f = f_local a_id ty in

  (* let m1 = EcEnv.Fun.prF_memenv m1_id fl env in *)
  (* let m2 = EcEnv.Fun.prF_memenv m2_id fr env in *)
  (* memories must be abstract??!! *)
  let m1 = m1_id,None in
  let m2 = m2_id,None in

  let smem1 = Fsubst.f_bind_mem Fsubst.f_subst_id mleft mhr in
  let smem2 = Fsubst.f_bind_mem Fsubst.f_subst_id mright mhr in
  let phi1 = Fsubst.f_subst smem1 phi_l in
  let phi2 = Fsubst.f_subst smem2 phi_r in
  let pr1 = f_pr m1_id fl (List.map snd argsl) (f_eq a_f phi1) in
  let pr2 = f_pr m2_id fr (List.map snd argsr) (f_eq a_f phi2) in

  let concl_pr = f_eq pr1 pr2 in
  let smem =  
    Fsubst.f_bind_mem (Fsubst.f_bind_mem Fsubst.f_subst_id mright m2_id) mleft m1_id
  in
  let pre = Fsubst.f_subst smem ef.ef_pr in
  let concl =
    f_forall_mems
      [m1_id, EcMemory.memtype m1;m2_id,EcMemory.memtype m2] 
      (f_imp pre concl_pr) in
  let binders_l = List.map (fun ((v,t),_) -> v,GTty t ) argsl in
  let binders_r = List.map (fun ((v,t),_) -> v,GTty t ) argsr in
  let concl = f_forall_simpl binders_l (f_forall_simpl binders_r concl) in
  let concl = f_forall_simpl [a_id,GTty ty] concl in
  let concl_post = f_imps_simpl [f_eq phi_l a_f;f_eq phi_r a_f] ef.ef_po in
  let memenvl,_,memenvr,_,_ = Fun.equivS fl fr env in
  let concl_post = f_forall_mems [memenvl;memenvr] concl_post in
  let concl_post = f_forall_simpl [a_id,GTty ty] concl_post in
    prove_goal_by [concl_post;concl] (RN_xtd (new EcPhlDeno.rn_hl_deno)) g

(* -------------------------------------------------------------------- *)
let process_ppr (phi1,phi2) g =
  let hyps,concl = get_goal g in
  let ef = t_as_equivF concl in
  let _penv,qenv = LDecl.equivF ef.ef_fl ef.ef_fr hyps in
  let phi1 = process_form_opt qenv phi1 None in
  let phi2 = process_form_opt qenv phi2 None in
  (* TODO: check for type unification *)
  let ty = f_ty phi1 in
    t_ppr ty phi1 phi2 g
