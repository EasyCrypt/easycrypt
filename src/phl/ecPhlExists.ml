(* -------------------------------------------------------------------- *)
open EcUtils
open EcAst
open EcFol
open EcEnv
open EcSubst

open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal

module L   = EcLocation
module APT = EcParsetree
module TTC = EcProofTyping
module PT  = EcProofTerm

(* -------------------------------------------------------------------- *)
let get_to_gens fs =
  let do_id (f: inv) =
    let id =
      match f with
      | Inv_ss f -> begin match f.inv.f_node with
          | Fpvar (pv, m) -> 
            id_of_pv pv m
          | _             -> EcIdent.create "f" 
        end
      | Inv_ts f -> begin match f.inv.f_node with
          | Fpvar (pv, m) -> 
            id_of_pv ~mc:(f.ml, f.mr) pv m
          | _             -> EcIdent.create "f" 
        end in
    id, f in
  List.map do_id fs

(* -------------------------------------------------------------------- *)
let t_hr_exists_elim_r ?(bound : int option) (tc : tcenv1) =
  let pre = tc1_get_pre tc in
  let bd, pre' =
    try  destr_exists_prenex ?bound (inv_of_inv pre)
    with DestrError _ -> [], (inv_of_inv pre) in
  let pre = map_inv1 (fun _ -> pre') pre in
  let concl = f_forall bd (set_pre ~pre (FApi.tc1_goal tc)) in
  FApi.xmutate1 tc `HlExists [concl]

(* -------------------------------------------------------------------- *)
let t_hr_exists_intro_r fs tc =
  let hyps  = FApi.tc1_hyps tc in
  let concl = FApi.tc1_goal tc in
  let pre1  = tc1_get_pre  tc in
  let post  = tc1_get_post tc in
  let gen   = get_to_gens fs in
  let eqs   = List.map (fun (id, f) -> map_inv1 (f_eq (f_local id (inv_of_inv f).f_ty)) f) gen in
  let bd    = List.map (fun (id, f) -> (id, GTty (inv_of_inv f).f_ty)) gen in
  let is_ehoare =
    match concl.f_node with
    | FeHoareF _ | FeHoareS _ -> true
    | _ -> false in
  let pre   =
    let eqs = match eqs with 
      | [] -> map_inv1 (fun _ -> f_true) pre1
      | _ -> map_inv f_ands eqs in
    if is_ehoare then
      map_inv2 f_interp_ehoare_form (map_inv1 (f_exists bd) eqs) pre1
    else 
      map_inv1 (f_exists bd) (map_inv2 f_and eqs pre1) in

  let h = LDecl.fresh_id hyps "h" in
  let ml, mr = as_seq2 (LDecl.fresh_ids hyps ["&ml"; "&mr"]) in
  let m = LDecl.fresh_id hyps "&m" in
  let ms =
    match pre1 with
    | Inv_ts _ -> [ml; mr]
    | Inv_ss _ -> [m] in

  let inv_rebind f =
    match f with
    | Inv_ts f -> Inv_ts (ts_inv_rebind f ml mr)
    | Inv_ss f -> Inv_ss (ss_inv_rebind f m) in

  let args =
    let do1 (_, f) = PAFormula (inv_of_inv (inv_rebind f)) in
    List.map do1 gen
  in

  let t_exists =
    if is_ehoare then
       t_intros_i ms @!
       EcHiGoal.t_apply_prept (PT.Prept.uglob EcCoreLib.CI_Xreal.p_xle_cxr_l) @+
       [ t_exists_intro_s args @! t_trivial;
         t_trivial]
    else FApi.t_seqs  [t_intros_i (ms@[h]); t_exists_intro_s args; t_apply_hyp h]
  in

  let tactic =
    (EcPhlConseq.t_conseq pre post) @+
      [ t_exists;
        t_trivial;
        t_id]
  in
  FApi.t_internal tactic tc

(* -------------------------------------------------------------------- *)
let t_hr_exists_elim  = FApi.t_low0 "hr-exists-elim"  t_hr_exists_elim_r
let t_hr_exists_intro = FApi.t_low1 "hr-exists-intro" t_hr_exists_intro_r

(* -------------------------------------------------------------------- *)
let process_exists_intro ~(elim : bool) fs tc =
  let (hyps, concl) = FApi.tc1_flat tc in
  let penv, f_tr =
    match concl.f_node with
    | FhoareF {hf_f=f;hf_m=m} | FeHoareF {ehf_f=f; ehf_m=m} 
    | FbdHoareF {bhf_f=f; bhf_m=m} -> 
      fst (LDecl.hoareF m f hyps), Inv_ss {m; inv = f_true}
    | FhoareS {hs_m=(m,_) as me} | FeHoareS {ehs_m=(m,_) as me}
    | FbdHoareS {bhs_m=(m,_) as me} -> 
      LDecl.push_active_ss me hyps, Inv_ss {m; inv = f_true}
    | FequivF ef -> fst (LDecl.equivF ef.ef_ml ef.ef_mr ef.ef_fl ef.ef_fr hyps), 
        Inv_ts {ml=ef.ef_ml; mr=ef.ef_mr; inv=f_true}
    | FequivS es -> LDecl.push_all [es.es_ml; es.es_mr] hyps, 
        Inv_ts {ml=(fst es.es_ml); mr=(fst es.es_mr); inv=f_true}
    | _ -> tc_error_noXhl ~kinds:hlkinds_Xhl !!tc
  in

  let fs =
    List.map
      (fun f -> map_inv1 (fun _ -> TTC.pf_process_form_opt !!tc penv None f) f_tr)
      fs
  in

  let tc = t_hr_exists_intro_r fs tc in

  if elim then
    t_hr_exists_elim_r ~bound:(List.length fs) (FApi.as_tcenv1 tc)
  else tc

(* -------------------------------------------------------------------- *)
let process_ecall oside (l, tvi, fs) tc =
  let (hyps, concl) = FApi.tc1_flat tc in

  let hyps, kind, f_tr =
    match concl.f_node with
    | FhoareS hs when is_none oside ->
        LDecl.push_active_ss hs.hs_m hyps, `Hoare (List.length hs.hs_s.s_node),
        Inv_ss {m = fst hs.hs_m; inv = f_true}
    | FequivS es ->
        let n1 = List.length es.es_sl.s_node in
        let n2 = List.length es.es_sr.s_node in
        LDecl.push_all [es.es_ml; es.es_mr] hyps, `Equiv (n1, n2),
        Inv_ts {ml = fst es.es_ml; mr = fst es.es_mr; inv = f_true}
    | _ -> tc_error_noXhl ~kinds:[`Hoare `Stmt; `Equiv `Stmt] !!tc
  in

  let t_local_seq p1 tc =
    match kind, oside, p1 with
    | `Hoare n, _, Inv_ss p1 ->
        EcPhlSeq.t_hoare_seq
          (Zpr.cpos (n-1)) p1 tc
    | `Equiv (n1, n2), None, Inv_ts p1 ->
        EcPhlSeq.t_equiv_seq
          (Zpr.cpos (n1-1), Zpr.cpos (n2-1)) p1 tc
    | `Equiv (n1, n2), Some `Left, Inv_ts p1 ->
        EcPhlSeq.t_equiv_seq
          (Zpr.cpos (n1-1), Zpr.cpos n2) p1 tc
    | `Equiv(n1, n2), Some `Right, Inv_ts p1 ->
        EcPhlSeq.t_equiv_seq
          (Zpr.cpos n1, Zpr.cpos (n2-1)) p1 tc
    | _ -> tc_error !!tc "mismatched sidedness or kind of conclusion"
  in

  let fs =
    List.map
      (fun f -> map_inv1 (fun _ -> TTC.pf_process_form_opt !!tc hyps None f) f_tr)
      fs
  in

  let ids, p1 =
    let sub = t_local_seq f_tr tc in

    let sub = FApi.t_rotate `Left 1 sub in
    let sub = FApi.t_focus (t_hr_exists_intro_r fs) sub in
    let sub = FApi.t_focus (t_hr_exists_elim_r ~bound:(List.length fs)) sub in

    let ids =
      try  fst (EcFol.destr_forall (FApi.tc_goal sub))
      with DestrError _ -> [] in
    let ids = List.map (snd_map gty_as_ty) ids in

    let nms = List.map (fun (_, x) -> (EcIdent.create "_", x)) ids in
    let sub = FApi.t_focus (EcLowGoal.t_intros_i (List.fst nms)) sub in
    let pte = PT.ptenv_of_penv (FApi.tc_hyps sub) !!tc in
    let pt  = PT.process_pterm pte (APT.FPNamed (l, tvi)) in

    let pt =
      List.fold_left (fun pt (id, ty) ->
          PT.apply_pterm_to_arg_r pt (PT.PVAFormula (f_local id ty)))
        pt ids in

    assert (PT.can_concretize pt.PT.ptev_env);
    let _pt, ax = PT.concretize pt in

    let sub = FApi.t_focus (EcPhlCall.t_call oside ax) sub in
    let sub = FApi.t_rotate `Left 1 sub in
    let sub = oget (get_post (FApi.tc_goal sub)) in

    let subst =
      List.fold_left2
        (fun s id f -> add_flocal s id (inv_of_inv f))
        empty (List.fst ids) fs in

    (nms, subst_inv subst sub) in

  let tc = t_local_seq p1 tc in
  let tc = FApi.t_rotate `Left 1 tc in
  let tc = FApi.t_focus (t_hr_exists_intro_r fs) tc in
  let tc = FApi.t_focus (t_hr_exists_elim_r ~bound:(List.length fs)) tc in
  let tc = FApi.t_focus (EcLowGoal.t_intros_i (List.fst ids)) tc in

  let pte = PT.ptenv_of_penv (FApi.tc_hyps tc) (FApi.tc_penv tc) in
  let pt  = PT.process_pterm pte (APT.FPNamed (l, tvi)) in

  let pt =
    List.fold_left (fun pt (id, ty) ->
        PT.apply_pterm_to_arg_r pt (PT.PVAFormula (f_local id ty)))
      pt ids in

  assert (PT.can_concretize pt.PT.ptev_env);

  let pt, ax = PT.concretize pt in

  let tc = FApi.t_focus (EcPhlCall.t_call oside ax) tc in
  let tc = FApi.t_focus (EcLowGoal.Apply.t_apply_bwd_hi ~dpe:true pt) tc in

  FApi.t_last EcPhlAuto.t_auto (FApi.t_rotate `Right 1 tc)
