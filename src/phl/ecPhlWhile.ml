(* -------------------------------------------------------------------- *)
open EcUtils
open EcTypes
open EcFol
open EcBaseLogic
open EcLogic
open EcPV
open EcCorePhl
open EcCoreHiPhl

(* -------------------------------------------------------------------- *)
class rn_hl_while (_ : form) (_ : form option) (_ : (form * form) option) =
object
  inherit xrule "[hl] while"
end

let rn_hl_while x1 x2 x3 =
  RN_xtd (new rn_hl_while x1 x2 x3 :> xrule)

(* -------------------------------------------------------------------- *)  
let t_hoare_while inv g =
  let env, _, concl = get_goal_e g in
  let hs = t_as_hoareS concl in
  let ((e,c),s) = s_last_while "while" hs.hs_s in
  let m = EcMemory.memory hs.hs_m in
  let e = form_of_expr m e in
  (* the body preserve the invariant *)
  let b_pre  = f_and_simpl inv e in
  let b_post = inv in
  let b_concl = f_hoareS hs.hs_m b_pre c b_post in
  (* the wp of the while *)
  let post = f_imps_simpl [f_not_simpl e; inv] hs.hs_po in
  let modi = s_write env c in
  let post = generalize_mod env m modi post in
  let post = f_and_simpl inv post in
  let concl = f_hoareS_r { hs with hs_s = s; hs_po=post} in
    prove_goal_by [b_concl;concl] (rn_hl_while inv None None) g

let t_bdHoare_while inv vrnt g =
  let env, _, concl = get_goal_e g in
  let bhs = t_as_bdHoareS concl in
  let ((e,c),s) = s_last_while "while" bhs.bhs_s in
  let m = EcMemory.memory bhs.bhs_m in
  let e = form_of_expr m e in
  (* the body preserve the invariant *)
  let k_id = EcIdent.create "z" in
  let k = f_local k_id tint in
  let vrnt_eq_k = f_eq vrnt k in
  let vrnt_lt_k = f_int_lt vrnt k in
  let b_pre  = f_and_simpl (f_and_simpl inv e) vrnt_eq_k in
  let b_post = f_and_simpl inv vrnt_lt_k in
  let b_concl = f_bdHoareS_r 
    { bhs with
        bhs_pr  = b_pre; bhs_s  = c; bhs_po = b_post;
        bhs_cmp = FHeq ; bhs_bd = f_r1}
  in
  let b_concl = f_forall_simpl [(k_id,GTty tint)] b_concl in
  (* the wp of the while *)
  let post = f_imps_simpl [f_not_simpl e; inv] bhs.bhs_po in
  let term_condition = f_imps_simpl [inv;f_int_le vrnt (f_int 0)] (f_not_simpl e) in
  let post = f_and term_condition post in
  let modi = s_write env c in
  let post = generalize_mod env m modi post in
  let post = f_and_simpl inv post in
  let concl = f_bdHoareS_r { bhs with bhs_s = s; bhs_po=post} in
  prove_goal_by [b_concl;concl] (rn_hl_while inv (Some vrnt) None) g


let t_bdHoare_while_rev inv (juc,n as g) =
  let env, hyps, concl = get_goal_e g in
  let bhs = t_as_bdHoareS concl in
  if (bhs.bhs_cmp <> FHle) then 
    tacuerror "only upper-bounded judgments are supported";
  let b_pre  = bhs.bhs_pr in
  let b_post = bhs.bhs_po in
  let mem = bhs.bhs_m in
  let ((loopGuardExp,loopBody),rem_s) = s_last_while "while" bhs.bhs_s in
  let loopGuard = form_of_expr (EcMemory.memory mem) loopGuardExp in
  let bound = bhs.bhs_bd in

  let w_u = EcPV.while_info env loopGuardExp loopBody in
  let w   = EcEnv.LDecl.fresh_id hyps "w" in
  let hyps' = EcEnv.LDecl.add_local w (EcBaseLogic.LD_abs_st w_u) hyps in

  let body_concl = 
    let while_s = EcModules.stmt [EcModules.i_abstract w] in
    let while_s' = 
      EcModules.stmt 
        [EcModules.i_if (loopGuardExp, while_s, EcModules.stmt [])] in
    let unfolded_while_s = EcModules.s_seq loopBody while_s' in
    let while_jgmt = f_bdHoareS_r {bhs with bhs_pr=inv ; bhs_s=while_s' } in
    let unfolded_while_jgmt = f_bdHoareS_r 
      {bhs with bhs_pr=f_and inv loopGuard; bhs_s=unfolded_while_s } in
    f_imp while_jgmt unfolded_while_jgmt
  in

  let rem_post = 
    let term_post = f_imp (f_and inv (f_and (f_not loopGuard) b_post)) 
      (f_eq bound f_r1)
    in
    let modi = s_write env loopBody in
    let term_post = generalize_mod env (EcMemory.memory mem) modi term_post in
    f_and inv term_post
  in
  let rem_concl = f_hoareS mem b_pre rem_s rem_post in
  let juc,n1 = new_goal juc (hyps',body_concl) in
  let juc,n2 = new_goal juc (hyps, rem_concl) in
  let rule = { pr_name =  (rn_hl_while inv None None);
               pr_hyps = [RA_node n1; RA_node n2] } in
  upd_rule rule (juc, n)


let t_bdHoare_while_rev_geq inv vrnt k eps (juc,n as g) =
  let env, hyps, concl = get_goal_e g in
  let bhs = t_as_bdHoareS concl in
  (* The test is not necessary : 
     the rule is valid for <= (more hypothesis than the previous one),
     So it is valid for = 
  *)
(*  if (bhs.bhs_cmp <> FHge) then 
    tacuerror "only lower-bounded judgments are accepted for these parameters"; *)
  let b_pre  = bhs.bhs_pr in
  let b_post = bhs.bhs_po in
  let mem = bhs.bhs_m in
  let ((loopGuardExp,loopBody),rem_s) = s_last_while "while" bhs.bhs_s in
  if ( not (EcModules.s_equal rem_s (EcModules.stmt []) )) then 
      tacuerror 
        "only single loop statements are accepted with these parameters";
  let loopGuard = form_of_expr (EcMemory.memory mem) loopGuardExp in
  let bound = bhs.bhs_bd in
  let modi = s_write env loopBody in
  let pre_inv_concl = f_imp b_pre inv in
  let pre_bound_concl = 
    let term_post = 
      f_imps [b_pre; f_not loopGuard; f_not b_post] (f_eq bound f_r0) in
    f_forall_mems [mem] 
      (generalize_mod env (EcMemory.memory mem) modi term_post)
  in
  let inv_term_concl = 
    let concl= f_imp inv (
      f_and (f_int_le vrnt k) (f_imp (f_int_le vrnt f_i0) (f_not loopGuard))) 
    in
    f_forall_mems [mem] (generalize_mod env (EcMemory.memory mem) modi concl)
  in
  let vrnt_concl = 
    let k_id = EcIdent.create "z" in
    let k = f_local k_id tint in
    let vrnt_eq_k = f_eq vrnt k in
    let vrnt_lt_k = f_int_lt vrnt k in
    f_forall_simpl [(k_id,GTty tint)] (f_bdHoareS_r {bhs with bhs_pr=f_ands [inv;loopGuard;vrnt_eq_k];
      bhs_po=vrnt_lt_k;  bhs_s=loopBody; bhs_cmp=FHge; bhs_bd=eps } )
  in

  let inv_concl = 
    f_bdHoareS_r {bhs with bhs_pr=f_and inv loopGuard; bhs_po=inv; 
      bhs_s=loopBody; bhs_cmp=FHeq; bhs_bd=f_r1 }
  in

  let w_u = EcPV.while_info env loopGuardExp loopBody in
  let w   = EcEnv.LDecl.fresh_id hyps "w" in
  let hyps' = EcEnv.LDecl.add_local w (EcBaseLogic.LD_abs_st w_u) hyps in
  
  let body_concl = 
    let while_s = EcModules.stmt [EcModules.i_abstract w] in
    let while_s' = 
      EcModules.stmt 
        [EcModules.i_if (loopGuardExp, while_s, EcModules.stmt [])] in
    let unfolded_while_s = EcModules.s_seq loopBody while_s' in
    let while_jgmt = f_bdHoareS_r {bhs with bhs_pr=inv ; bhs_s=while_s' } in
    let unfolded_while_jgmt = f_bdHoareS_r 
      {bhs with bhs_pr=f_and inv loopGuard; bhs_s=unfolded_while_s } in
    f_imp while_jgmt unfolded_while_jgmt
  in

  let juc,n1 = new_goal juc (hyps,  pre_inv_concl) in
  let juc,n2 = new_goal juc (hyps,  pre_bound_concl) in
  let juc,n3 = new_goal juc (hyps,  inv_term_concl) in
  let juc,n4 = new_goal juc (hyps', body_concl) in
  let juc,n5 = new_goal juc (hyps,  inv_concl) in
  let juc,n6 = new_goal juc (hyps,  vrnt_concl) in
  let rule = { pr_name =  (rn_hl_while inv None None);
               pr_hyps = [RA_node n1; RA_node n2;RA_node n3;RA_node n4;
                          RA_node n5;RA_node n6] } in
  upd_rule rule (juc, n)
 

let t_equiv_while_disj side vrnt inv g =
  let env, _, concl = get_goal_e g in
  let es = t_as_equivS concl in
  let s,m_side,m_other = if side then es.es_sl, es.es_ml, es.es_mr 
    else es.es_sr, es.es_mr, es.es_ml in
  let ((e,c),s) = s_last_while "while" s in
  let e = form_of_expr (EcMemory.memory m_side) e in
  (* the body preserve the invariant and variant decreases *)
  let k_id = EcIdent.create "z" in
  let k = f_local k_id tint in
  let vrnt_eq_k = f_eq vrnt k in
  let vrnt_lt_k = f_int_lt vrnt k in
  let m_other' = EcIdent.create "&m",EcMemory.memtype m_other in
  let smem = Fsubst.f_bind_mem Fsubst.f_subst_id (EcMemory.memory m_side) mhr in
  let smem = Fsubst.f_bind_mem smem (EcMemory.memory m_other) (EcMemory.memory m_other') in
  let b_pre  = f_and_simpl (f_and_simpl inv e) vrnt_eq_k in
  let b_pre = Fsubst.f_subst smem b_pre in
  let b_post = f_and_simpl inv vrnt_lt_k in
  let b_post = Fsubst.f_subst smem b_post in
  let b_concl = f_bdHoareS (mhr,EcMemory.memtype m_side) b_pre c b_post FHeq f_r1 in 
  let b_concl = f_forall_simpl [(k_id,GTty tint)] b_concl in
  let b_concl = f_forall_mems [m_other'] b_concl in
  (* the wp of the while *)
  let post = f_imps_simpl [f_not_simpl e; inv] es.es_po in
  let term_condition = f_imps_simpl [inv;f_int_le vrnt (f_int 0)] (f_not_simpl e) in
  let post = f_and term_condition post in
  let modi = s_write env c in
  let post = generalize_mod env (EcMemory.memory m_side) modi post in
  let post = f_and_simpl inv post in
  let concl =
    if   side
    then f_equivS_r { es with es_sl = s; es_po=post}
    else f_equivS_r { es with es_sr = s; es_po=post}
  in
    prove_goal_by [b_concl;concl] (rn_hl_while inv (Some vrnt) None) g

let t_equiv_while inv g =
  let env,_,concl = get_goal_e g in
  let es = t_as_equivS concl in
  let (el,cl), (er,cr), sl, sr = s_last_whiles "while" es.es_sl es.es_sr in
  let ml = EcMemory.memory es.es_ml in
  let mr = EcMemory.memory es.es_mr in
  let el = form_of_expr ml el in
  let er = form_of_expr mr er in
  let sync_cond = f_iff_simpl el er in
  (* the body preserve the invariant *)
  let b_pre  = f_ands_simpl [inv; el] er in
  let b_post = f_and_simpl inv sync_cond in
  let b_concl = f_equivS es.es_ml es.es_mr b_pre cl cr b_post in
  (* the wp of the while *)
  let post = f_imps_simpl [f_not_simpl el;f_not_simpl er; inv] es.es_po in
  let modil = s_write env cl in
  let modir = s_write env cr in
  let post = generalize_mod env mr modir post in
  let post = generalize_mod env ml modil post in
  let post = f_and_simpl inv post in
  let concl = f_equivS_r {es with es_sl = sl; es_sr = sr; es_po = post} in
    prove_goal_by [b_concl; concl] (rn_hl_while inv None None) g 

(* -------------------------------------------------------------------- *)

(*

CASE (1): (t_bdHoare_while)

[c': P ==> Inv /\ forall Mod, ( (Inv/\!b -> Q) /\ (Inv/\vrnt<=0 -> !b) )  ] <> p
[c : Inv /\ b /\ vrnt=k ==> Inv /\ vrnt<k ] = 1
================================================================================
[c';while b do c : P ==> Q ] <> p


CASE (2): (t_bdHoare_while_rev)

c': P ==> Inv /\ forall Mod', ( (Inv/\!b /\ Q) -> p=1)[Mod'/Mod]
[while b do c : Inv ==> Q] <= p -> 
  [c; while b do c : Inv /\ b ==> Q] <= p
================================================================================
[c';while b do c : P ==> Q ] <= p


*)

let process_while side_opt phi vrnt_opt o_info g =
  match (get_concl g).f_node with
  | FhoareS _ -> begin
    match vrnt_opt with
    | None -> t_hoare_while (process_phl_formula g phi) g
    | _    -> cannot_apply "while" "wrong arguments"
    end

  | FbdHoareS _ -> begin
      match vrnt_opt, o_info with
      | Some vrnt, None -> (* this pattern is reserved for case (1) *)
          t_bdHoare_while 
            (process_phl_formula g phi) 
            (process_phl_form tint g vrnt) 
            g
      | Some vrnt, Some (k,eps) ->
        t_bdHoare_while_rev_geq
          (process_phl_formula g phi) 
          (process_phl_form tint g vrnt) 
          (process_phl_form tint g k) 
          (process_phl_form treal g eps) 
          g
      | None, None -> (* this pattern corresponds to case (2) *)
        t_bdHoare_while_rev 
          (process_phl_formula g phi) 
          g
      | None, Some _ -> tacuerror "wrong tactic parameters"
  end

  | FequivS _ -> begin
      match side_opt, vrnt_opt with
      | None, None ->
          t_equiv_while (process_prhl_formula g phi) g
      | Some side, Some vrnt ->
          t_equiv_while_disj side
            (process_prhl_form tint g vrnt)
            (process_prhl_formula g phi)
            g
      | _ -> cannot_apply "while" "wrong arguments"
  end

  | _ -> cannot_apply "while" "the conclusion is not a hoare or a equiv"
