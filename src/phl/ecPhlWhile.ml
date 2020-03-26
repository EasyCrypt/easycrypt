(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
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
module EP  = EcParsetree
module Mid = EcIdent.Mid

(* -------------------------------------------------------------------- *)
let while_info env e s =
  let rec i_info (w,r,c) i =
    match i.i_node with
    | Sasgn(lp, e) | Srnd(lp, e) ->
        let r = e_read_r env r e in
        let w = lp_write_r env w lp in
        (w, r, c)

    | Sif (e, s1, s2) ->
        let r = e_read_r env r e in s_info (s_info (w, r, c) s1) s2

    | Swhile(e,s) ->
        let r = e_read_r env r e in s_info (w, r, c) s

    | Scall(lp,f,es) ->
        let r = List.fold_left (e_read_r env) r es in
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

  { EcModules.aus_reads  = fst (PV.ntr_elements r);
    EcModules.aus_writes = fst (PV.ntr_elements w);
    EcModules.aus_calls  = Sx.ntr_elements c; }

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
  let { EP.wh_inv  = phi ;
        EP.wh_vrnt = vrnt;
        EP.wh_bds  = bds ; } = winfos in

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

(* -------------------------------------------------------------------- *)
module ASyncWhile = struct
  exception CannotTranslate

  let form_of_expr env mother mh =
    let map = ref (Mid.add mother (EcPV.PVMap.create env) Mid.empty) in

    let rec aux fp =
      match fp.f_node with
      | Fint   z -> e_int z
      | Flocal x -> e_local x fp.f_ty

      | Fop  (p, tys) -> e_op p tys fp.f_ty
      | Fapp (f, fs)  -> e_app (aux f) (List.map aux fs) fp.f_ty
      | Ftuple fs     -> e_tuple (List.map aux fs)
      | Fproj  (f, i) -> e_proj (aux f) i fp.f_ty

      | Fif (c, f1, f2) ->
         e_if (aux c) (aux f1) (aux f2)

      | Fmatch (c, bs, ty) ->
         e_match (aux c) (List.map aux bs) ty

      | Flet (lp, f1, f2) ->
         e_let lp (aux f1) (aux f2)

      | Fquant (kd, bds, f) ->
         e_quantif (auxkd kd) (List.map auxbd bds) (aux f)

      | Fpvar (pv, m) ->
         if EcIdent.id_equal m mh then
           e_var pv fp.f_ty
         else
           let bds = odfl (EcPV.PVMap.create env) (Mid.find_opt m !map) in
           let idx =
             match EcPV.PVMap.find pv bds with
             | None ->
                 let pfx = EcIdent.name m in
                 let pfx = String.sub pfx  1 (String.length pfx - 1) in
                 let x   = EcPath.basename pv.pv_name.EcPath.x_sub in
                 let x   = EcIdent.create (x ^ "_" ^ pfx) in
                 let bds = EcPV.PVMap.add pv (x, fp.f_ty) bds in
                 map := Mid.add m bds !map; x
             | Some (x, _) -> x

           in e_local idx fp.f_ty

      | Fglob     _
      | FhoareF   _ | FhoareS   _
      | FbdHoareF _ | FbdHoareS _
      | FequivF   _ | FequivS   _
      | FeagerF   _ | Fpr       _ -> raise CannotTranslate

    and auxkd (kd : quantif) : equantif =
      match kd with
      | Lforall -> `EForall
      | Lexists -> `EExists
      | Llambda -> `ELambda

    and auxbd ((x, bd) : binding) =
      match bd with
      | GTty ty -> (x, ty)
      | _ -> raise CannotTranslate

    in fun f -> let e = aux f in (e, !map)
end

(* -------------------------------------------------------------------- *)
let process_async_while (winfos : EP.async_while_info) tc =
  let e_and e1 e2 =
    let p = EcCoreLib.CI_Bool.p_and in
    e_app (e_op p [] (toarrow [tbool; tbool] tbool)) [e1; e2] tbool
  in

  let { EP.asw_inv  = inv     ;
        EP.asw_test = ((t1,f1), (t2,f2));
        EP.asw_pred = (p0, p1); } = winfos in

  let evs  = tc1_as_equivS tc in
  let env  = FApi.tc1_env  tc in
  let hyps = FApi.tc1_hyps tc in

  let ml = EcMemory.memory evs.es_ml in
  let mr = EcMemory.memory evs.es_mr in

  let (el, cl), sl = tc1_last_while tc evs.es_sl in
  let (er, cr), sr = tc1_last_while tc evs.es_sr in

  let inv = TTC.tc1_process_prhl_formula tc inv in
  let p0  = TTC.tc1_process_prhl_formula tc  p0 in
  let p1  = TTC.tc1_process_prhl_formula tc  p1 in
  let f1  = TTC.tc1_process_prhl_form_opt tc None f1 in
  let f2  = TTC.tc1_process_prhl_form_opt tc None f2 in
  let t1  = TTC.tc1_process_Xhl_exp tc (Some `Left ) (Some (tfun f1.f_ty tbool)) t1 in
  let t2  = TTC.tc1_process_Xhl_exp tc (Some `Right) (Some (tfun f2.f_ty tbool)) t2 in
  let ft1 = form_of_expr ml t1 in
  let ft2 = form_of_expr mr t2 in
  let fe1 = form_of_expr ml el in
  let fe2 = form_of_expr mr er in
  let fe  = f_or fe1 fe2 in

  let cond1 = f_forall_mems [evs.es_ml; evs.es_mr]
    (f_imps [inv; fe; p0] (f_ands [fe1; fe2;
                                   f_app ft1 [f1] tbool;
                                   f_app ft2 [f2] tbool])) in

  let cond2 = f_forall_mems [evs.es_ml; evs.es_mr]
    (f_imps [inv; fe; f_not p0; p1] fe1) in

  let cond3 = f_forall_mems [evs.es_ml; evs.es_mr]
    (f_imps [inv; fe; f_not p0; f_not p1] fe2) in

  let xwh =
    let v1, v2 = as_seq2 (EcEnv.LDecl.fresh_ids hyps ["v1_"; "v2_"]) in
    let fv1 = f_local v1 f1.f_ty in
    let fv2 = f_local v2 f2.f_ty in
    let ev1 = e_local v1 f1.f_ty in
    let ev2 = e_local v2 f2.f_ty in
    let eq1 = f_eq fv1 f1 and eq2 = f_eq fv2 f2 in
    let pr = f_ands [inv; fe; p0; eq1; eq2] in
    let po = inv in
    let wl = s_while (e_and el (e_app t1 [ev1] tbool), cl) in
    let wr = s_while (e_and er (e_app t2 [ev2] tbool), cr) in
    EcFol.f_forall [(v1, GTty f1.f_ty); (v2, GTty f2.f_ty)]
      (f_equivS evs.es_ml evs.es_mr pr wl wr po)
  in

  let hr1, hr2 =
    let hr1 =
      let subst = Fsubst.f_bind_mem Fsubst.f_subst_id ml mhr in
      let inv   = Fsubst.f_subst subst inv in
      let p0    = Fsubst.f_subst subst p0  in
      let p1    = Fsubst.f_subst subst p1  in

      let pre = f_ands [inv; form_of_expr mhr el; f_not p0; p1] in
      f_forall_mems [evs.es_mr]
        (f_hoareS (mhr, EcMemory.memtype evs.es_ml) pre cl inv)

    and hr2 =
      let subst = Fsubst.f_bind_mem Fsubst.f_subst_id mr mhr in
      let inv   = Fsubst.f_subst subst inv in
      let p0    = Fsubst.f_subst subst p0  in
      let p1    = Fsubst.f_subst subst p1  in

      let pre = f_ands [inv; form_of_expr mhr er; f_not p0; f_not p1] in
      f_forall_mems [evs.es_ml]
        (f_hoareS (mhr, EcMemory.memtype evs.es_mr) pre cr inv)

    in (hr1, hr2)
  in

  let xhyps =
    let mtypes = Mid.of_list [evs.es_ml; evs.es_mr] in

    fun m fp ->
      let fp =
        Mid.fold (fun mh pvs fp ->
          let mty = Mid.find_opt mh mtypes in
          let fp  =
            EcPV.Mnpv.fold (fun pv (x, ty) fp ->
              f_let1 x (f_pvar pv ty mh) fp)
            (EcPV.PVMap.raw pvs) fp
          in f_forall_mems [mh, oget mty] fp)
        m fp
      and cnt =
        Mid.fold
          (fun _ pvs i -> i + 1 + EcPV.Mnpv.cardinal (EcPV.PVMap.raw pvs))
          m 0
      in (cnt, fp)
  in

  let (c1, ll1), (c2, ll2) =
    try
      let ll1 =
        let subst   = Fsubst.f_bind_mem Fsubst.f_subst_id ml mhr in
        let inv     = Fsubst.f_subst subst inv in
        let test    = f_ands [fe1; f_not p0; p1] in
        let test, m = ASyncWhile.form_of_expr env (EcMemory.memory evs.es_mr) ml test in
        let c       = s_while (test, cl) in
        xhyps m
          (f_bdHoareS (mhr, EcMemory.memtype evs.es_ml) inv c f_true FHeq f_r1)

      and ll2 =
        let subst   = Fsubst.f_bind_mem Fsubst.f_subst_id mr mhr in
        let inv     = Fsubst.f_subst subst inv in
        let test    = f_ands [fe1; f_not p0; f_not p1] in
        let test, m = ASyncWhile.form_of_expr env (EcMemory.memory evs.es_ml) mr test in
        let c       = s_while (test, cr) in
        xhyps m
          (f_bdHoareS (mhr, EcMemory.memtype evs.es_mr) inv c f_true FHeq f_r1)

      in (ll1, ll2)

    with ASyncWhile.CannotTranslate ->
      tc_error !!tc
        "async-while linking predicates cannot be converted to expressions"
  in

  let concl =
    let post  = f_imps [f_not fe1; f_not fe2; inv] evs.es_po in
    let modil = s_write env cl in
    let modir = s_write env cr in
    let post  = generalize_mod env mr modir post in
    let post  = generalize_mod env ml modil post in
    f_equivS_r { evs with es_sl = sl; es_sr = sr; es_po = post; } in

  FApi.t_onfsub (function
    | 6 -> Some (EcLowGoal.t_intros_n c1)
    | 7 -> Some (EcLowGoal.t_intros_n c2)
    | _ -> None)

    (FApi.xmutate1
       tc `AsyncWhile
         [cond1; cond2; cond3; hr1; hr2; xwh; ll1; ll2; concl])
