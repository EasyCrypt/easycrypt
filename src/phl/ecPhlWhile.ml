(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcTypes
open EcFol
open EcModules
open EcPV

open EcCoreGoal
open EcLowPhlGoal

module Sx  = EcPath.Sx
module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
let while_info env e s =
  let rec i_info (w,r,c) i =
    match i.i_node with
    | Sasgn(lp, e) | Srnd(lp, e) ->
        let r = e_read_r env (EcPV.lp_read_r env r lp) e in
        let w = lp_write_r env w lp in
        (w, r, c)

    | Sif (e, s1, s2) ->
        let r = e_read_r env r e in s_info (s_info (w, r, c) s1) s2

    | Swhile(e,s) ->
        let r = e_read_r env r e in s_info (w, r, c) s

    | Scall(lp,f,es) ->
        let r = List.fold_left (e_read_r env) r es in
        let r = match lp with None -> r | Some lp -> lp_read_r  env r lp in
        let w = match lp with None -> w | Some lp -> lp_write_r env w lp in
        let f = EcEnv.NormMp.norm_xfun env f in
        (w, r, Sx.add f c)

    | Sassert e ->
        (w, e_read_r env r e, c)

    | Sabstract id ->
      let add_pv x (pv,ty) = PV.add env pv ty x in
      let us = EcEnv.AbsStmt.byid id env in
      let w = List.fold_left add_pv w us.EcModules.aus_writes in
      let r = List.fold_left add_pv r us.EcModules.aus_reads in
      let c = List.fold_left (fun c f -> Sx.add f c) c us.EcModules.aus_calls in
      (w, r, c)

  and s_info info s = List.fold_left i_info info s.s_node in

  let (w,r,c) = s_info (PV.empty, EcPV.e_read env e, Sx.empty) s in

  { EcModules.aus_reads  = fst (PV.elements r);
    EcModules.aus_writes = fst (PV.elements w);
    EcModules.aus_calls  = Sx.elements c; }

(* -------------------------------------------------------------------- *)
let t_hoare_while_r inv tc =
  let env = FApi.tc1_env tc in
  let hs = tc1_as_hoareS tc in
  let (e, c), s = tc1_last_while tc hs.hs_s in
  let m = EcMemory.memory hs.hs_m in
  let e = form_of_expr m e in
  (* the body preserves the invariant *)
  let b_pre  = f_and_simpl inv e in
  let b_post = inv in
  let b_concl = f_hoareS hs.hs_m b_pre c b_post in
  (* the wp of the while *)
  let post = f_imps_simpl [f_not_simpl e; inv] hs.hs_po in
  let modi = s_write env c in
  let post = generalize_mod env m modi post in
  let post = f_and_simpl inv post in
  let concl = f_hoareS_r { hs with hs_s = s; hs_po=post} in

  FApi.xmutate1 tc `While [b_concl; concl]

(* -------------------------------------------------------------------- *)
let t_bdhoare_while_r inv vrnt tc =
  let env = FApi.tc1_env tc in
  let bhs = tc1_as_bdhoareS tc in
  let (e, c), s = tc1_last_while tc bhs.bhs_s in
  let m = EcMemory.memory bhs.bhs_m in
  let e = form_of_expr m e in
  (* the body preserves the invariant *)
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
  let term_condition = f_imps_simpl [inv;f_int_le vrnt f_i0] (f_not_simpl e) in
  let post = f_and term_condition post in
  let modi = s_write env c in
  let post = generalize_mod env m modi post in
  let post = f_and_simpl inv post in
  let concl = f_bdHoareS_r { bhs with bhs_s = s; bhs_po=post} in

  FApi.xmutate1 tc `While [b_concl; concl]

(* -------------------------------------------------------------------- *)
let t_bdhoare_while_rev_r inv tc =
  let env, hyps, _ = FApi.tc1_eflat tc in
  let bhs = tc1_as_bdhoareS tc in

  if bhs.bhs_cmp <> FHle then
    tc_error !!tc "only judgments with an upper-bounded are supported";

  let b_pre  = bhs.bhs_pr in
  let b_post = bhs.bhs_po in
  let mem    = bhs.bhs_m in
  let bound  = bhs.bhs_bd in

  let (lp_guard_exp, lp_body), rem_s = tc1_last_while tc bhs.bhs_s in
  let lp_guard = form_of_expr (EcMemory.memory mem) lp_guard_exp in

  let w_u   = while_info env lp_guard_exp lp_body in
  let w     = EcEnv.LDecl.fresh_id hyps "w" in
  let hyps' = EcEnv.LDecl.add_local w (EcBaseLogic.LD_abs_st w_u) hyps in

  (* 1. Sub-goal *)
  let body_concl =
    let while_s  = EcModules.stmt [EcModules.i_abstract w] in
    let while_s' = EcModules.i_if (lp_guard_exp, while_s, EcModules.stmt []) in
    let while_s' = EcModules.stmt [while_s'] in
    let unfolded_while_s = EcModules.s_seq lp_body while_s' in
    let while_jgmt = f_bdHoareS_r {bhs with bhs_pr=inv ; bhs_s=while_s'; } in
    let unfolded_while_jgmt = f_bdHoareS_r
      { bhs with bhs_pr = f_and inv lp_guard; bhs_s = unfolded_while_s; }
    in
      f_imp while_jgmt unfolded_while_jgmt
  in

  (* 2. Sub-goal *)
  let rem_concl =
    let modi = s_write env lp_body in
    let term_post = f_imp
      (f_and inv (f_and (f_not lp_guard) b_post))
      (f_eq bound f_r1) in
    let term_post = generalize_mod env (EcMemory.memory mem) modi term_post in
    let term_post = f_and inv term_post in
    f_hoareS mem b_pre rem_s term_post
  in

  FApi.xmutate1_hyps tc `While [(hyps', body_concl); (hyps, rem_concl)]

(* -------------------------------------------------------------------- *)
let t_bdhoare_while_rev_geq_r inv vrnt k eps tc =
  let env, hyps, _ = FApi.tc1_eflat tc in

  let bhs    = tc1_as_bdhoareS tc in
  let b_pre  = bhs.bhs_pr in
  let b_post = bhs.bhs_po in
  let mem    = bhs.bhs_m in

  let (lp_guard_exp, lp_body), rem_s = tc1_last_while tc bhs.bhs_s in

  if not (List.is_empty rem_s.s_node) then
    tc_error !!tc  "only single loop statements are accepted";

  let lp_guard = form_of_expr (EcMemory.memory mem) lp_guard_exp in
  let bound    = bhs.bhs_bd in
  let modi     = s_write env lp_body in

  (* 1. Pre-invariant *)
  let pre_inv_concl = f_forall_mems [mem] (f_imp b_pre inv) in

  (* 2. Pre-bound *)
  let pre_bound_concl =
    let term_post = [b_pre; f_not lp_guard; f_not b_post] in
    let term_post = f_imps term_post (f_eq bound f_r0) in
    let term_post = generalize_mod env (EcMemory.memory mem) modi term_post in
      f_forall_mems [mem] term_post
  in

  (* 3. Term-invariant *)
  let inv_term_concl =
    let concl = f_imp (f_int_le vrnt f_i0) (f_not lp_guard) in
    let concl = f_and (f_int_le vrnt k) concl in
    let concl = f_imp inv concl in
      f_forall_mems [mem] (generalize_mod env (EcMemory.memory mem) modi concl)
  in

  (* 4. Vrnt conclusion *)
  let vrnt_concl =
    let k_id = EcIdent.create "z" in
    let k    = f_local k_id tint in
    let vrnt_eq_k = f_eq vrnt k in
    let vrnt_lt_k = f_int_lt vrnt k in
      f_and
        (f_forall_mems [mem] (f_imp inv (f_real_lt f_r0 eps)))
        (f_forall_simpl [(k_id,GTty tint)]
           (f_bdHoareS_r { bhs with
             bhs_pr  = f_ands [inv;lp_guard;vrnt_eq_k];
             bhs_po  = vrnt_lt_k;
             bhs_s   = lp_body;
             bhs_cmp = FHge;
             bhs_bd  = eps }))
  in

  (* 5. Out invariant *)
  let inv_concl =
    f_bdHoareS_r { bhs with
      bhs_pr  = f_and inv lp_guard;
      bhs_po  = inv;
      bhs_s   = lp_body;
      bhs_cmp = FHeq;
      bhs_bd  = f_r1; }
  in

  (* 6. Out body *)
  let w_u = while_info env lp_guard_exp lp_body in
  let w   = EcEnv.LDecl.fresh_id hyps "w" in
  let hyps' = EcEnv.LDecl.add_local w (EcBaseLogic.LD_abs_st w_u) hyps in

  let body_concl =
    let while_s1 = EcModules.stmt [EcModules.i_abstract w] in
    let while_s2 = EcModules.i_if (lp_guard_exp, while_s1, EcModules.stmt []) in
    let while_s2 = EcModules.stmt [while_s2] in

    let unfolded_while_s = EcModules.s_seq lp_body while_s2 in
    let while_jgmt = f_bdHoareS_r { bhs with bhs_pr=inv; bhs_s=while_s2; } in
    let unfolded_while_jgmt = f_bdHoareS_r
      { bhs with bhs_pr=f_and inv lp_guard; bhs_s=unfolded_while_s; }
    in
    f_imp while_jgmt unfolded_while_jgmt
  in

  FApi.xmutate1_hyps tc `While
    [(hyps , pre_inv_concl  );
     (hyps , pre_bound_concl);
     (hyps , inv_term_concl );
     (hyps', body_concl     );
     (hyps , inv_concl      );
     (hyps , vrnt_concl     )]

(* -------------------------------------------------------------------- *)
let t_equiv_while_disj_r side vrnt inv tc =
  let env = FApi.tc1_env tc in
  let es = tc1_as_equivS tc in
  let s, m_side, m_other =
    match side with
    | `Left  -> es.es_sl, es.es_ml, es.es_mr
    | `Right -> es.es_sr, es.es_mr, es.es_ml in
  let (e, c), s = tc1_last_while tc s in
  let e = form_of_expr (EcMemory.memory m_side) e in

  (* 1. The body preserves the invariant and the variant decreases. *)
  let k_id = EcIdent.create "z" in
  let k    = f_local k_id tint in

  let vrnt_eq_k = f_eq vrnt k in
  let vrnt_lt_k = f_int_lt vrnt k in

  let m_other' = (EcIdent.create "&m", EcMemory.memtype m_other) in

  let smem = Fsubst.f_subst_id in
  let smem = Fsubst.f_bind_mem smem (EcMemory.memory m_side ) mhr in
  let smem = Fsubst.f_bind_mem smem (EcMemory.memory m_other) (EcMemory.memory m_other') in

  let b_pre   = f_and_simpl (f_and_simpl inv e) vrnt_eq_k in
  let b_pre   = Fsubst.f_subst smem b_pre in
  let b_post  = f_and_simpl inv vrnt_lt_k in
  let b_post  = Fsubst.f_subst smem b_post in
  let b_concl = f_bdHoareS (mhr, EcMemory.memtype m_side) b_pre c b_post FHeq f_r1 in
  let b_concl = f_forall_simpl [(k_id,GTty tint)] b_concl in
  let b_concl = f_forall_mems [m_other'] b_concl in

  (* 2. WP of the while *)
  let post = f_imps_simpl [f_not_simpl e; inv] es.es_po in
  let term_condition = f_imps_simpl [inv;f_int_le vrnt f_i0] (f_not_simpl e) in
  let post = f_and term_condition post in
  let modi = s_write env c in
  let post = generalize_mod env (EcMemory.memory m_side) modi post in
  let post = f_and_simpl inv post in
  let concl =
    match side with
    | `Left  -> f_equivS_r { es with es_sl = s; es_po=post; }
    | `Right -> f_equivS_r { es with es_sr = s; es_po=post; }
  in

  FApi.xmutate1 tc `While [b_concl; concl]

(* -------------------------------------------------------------------- *)
let t_equiv_while_r inv tc =
  let env = FApi.tc1_env tc in
  let es = tc1_as_equivS tc in
  let (el, cl), sl = tc1_last_while tc es.es_sl in
  let (er, cr), sr = tc1_last_while tc es.es_sr in
  let ml = EcMemory.memory es.es_ml in
  let mr = EcMemory.memory es.es_mr in
  let el = form_of_expr ml el in
  let er = form_of_expr mr er in
  let sync_cond = f_iff_simpl el er in

  (* 1. The body preserves the invariant *)
  let b_pre  = f_ands_simpl [inv; el] er in
  let b_post = f_and_simpl inv sync_cond in
  let b_concl = f_equivS es.es_ml es.es_mr b_pre cl cr b_post in

  (* 2. WP of the while *)
  let post = f_imps_simpl [f_not_simpl el;f_not_simpl er; inv] es.es_po in
  let modil = s_write env cl in
  let modir = s_write env cr in
  let post = generalize_mod env mr modir post in
  let post = generalize_mod env ml modil post in
  let post = f_and_simpl b_post post in
  let concl = f_equivS_r { es with es_sl = sl; es_sr = sr; es_po = post; } in

  FApi.xmutate1 tc `While [b_concl; concl]

(* -------------------------------------------------------------------- *)
let t_hoare_while           = FApi.t_low1 "hoare-while"   t_hoare_while_r
let t_bdhoare_while         = FApi.t_low2 "bdhoare-while" t_bdhoare_while_r
let t_bdhoare_while_rev_geq = FApi.t_low4 "bdhoare-while" t_bdhoare_while_rev_geq_r
let t_bdhoare_while_rev     = FApi.t_low1 "bdhoare-while" t_bdhoare_while_rev_r
let t_equiv_while           = FApi.t_low1 "equiv-while"   t_equiv_while_r
let t_equiv_while_disj      = FApi.t_low3 "equiv-while"   t_equiv_while_disj_r

(* -------------------------------------------------------------------- *)
let process_while side winfos tc =
  let { EcParsetree.wh_inv  = phi ;
        EcParsetree.wh_vrnt = vrnt;
        EcParsetree.wh_bds  = bds ; } = winfos in

  match (FApi.tc1_goal tc).f_node with
  | FhoareS _ -> begin
      match vrnt with
      | None -> t_hoare_while (TTC.tc1_process_Xhl_formula tc phi) tc
      | _    -> tc_error !!tc "invalid arguments"
    end

  | FbdHoareS _ -> begin
      match vrnt, bds with
      | Some vrnt, None ->
          t_bdhoare_while
            (TTC.tc1_process_Xhl_formula tc phi)
            (TTC.tc1_process_Xhl_form tc tint vrnt)
            tc

      | Some vrnt, Some (k, eps) ->
        t_bdhoare_while_rev_geq
          (TTC.tc1_process_Xhl_formula tc phi)
          (TTC.tc1_process_Xhl_form    tc tint vrnt)
          (TTC.tc1_process_Xhl_form    tc tint k)
          (TTC.tc1_process_Xhl_form    tc treal eps)
          tc

      | None, None ->
          t_bdhoare_while_rev (TTC.tc1_process_Xhl_formula tc phi) tc

      | None, Some _ -> tc_error !!tc "invalid arguments"
  end

  | FequivS _ -> begin
      match side, vrnt with
      | None, None ->
          t_equiv_while (TTC.tc1_process_prhl_formula tc phi) tc

      | Some side, Some vrnt ->
          t_equiv_while_disj side
            (TTC.tc1_process_prhl_form    tc tint vrnt)
            (TTC.tc1_process_prhl_formula tc phi)
            tc

      | _ -> tc_error !!tc "invalid arguments"
  end

  | _ -> tc_error !!tc "expecting a hoare[...]/equiv[...]"
