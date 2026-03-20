(* -------------------------------------------------------------------- *)
open EcUtils
open EcAst
open EcFol
open EcEnv
open EcSubst

open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal
open EcMatching.Position

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
        end
      | Inv_hs _ -> assert false
    in
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
    | Inv_ss _ -> [m]
    | Inv_hs _ -> assert false
  in

  let inv_rebind f =
    match f with
    | Inv_ts f -> Inv_ts (ts_inv_rebind f ml mr)
    | Inv_ss f -> Inv_ss (ss_inv_rebind f m)
    | Inv_hs f -> Inv_hs (hs_inv_rebind f m)
  in

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
type call = EcModules.lvalue option * EcPath.xpath * EcTypes.expr list

type calls = [
  | `Single of call
  | `Double of call * call
]

(* -------------------------------------------------------------------- *)
let check_contract_type
  ?(loc      : L.t option)
  ?(phoare   : bool = false)
  ?(noexn    : bool = true)
  ~(name     : EcSymbols.qsymbol)
   (pe       : proofenv)
   (hyps     : LDecl.hyps)
   (calls    : calls)
   (contract : form)
=
  let env = LDecl.toenv hyps in

  let contract =
    EcReduction.h_red_opt EcReduction.full_red hyps contract
    |> odfl contract in

  match calls with
  | `Single (_, funname, _) -> begin
    let cttfname =
      match contract.f_node with
      | FhoareF hf ->
        if noexn then begin
          if not (POE.is_empty (hf_po hf).hsi_inv) then
            tc_error ?loc pe
              "contract must have an empty exception post-condition";
          end;      
        hf.hf_f
      | FbdHoareF hf when phoare -> hf.bhf_f
      | _ ->
        tc_error_lazy ?loc pe (fun fmt ->
          Format.fprintf fmt
            "contract %a should be a Hoare statement"
            EcSymbols.pp_qsymbol name
        )
    in
    if not (EcReduction.EqTest.for_xp env funname cttfname) then begin
      tc_error_lazy ?loc pe (fun fmt ->
        let ppe = EcPrinting.PPEnv.ofenv env in
        Format.fprintf fmt
          "contract %a should be for the procedure %a, not %a"
          EcSymbols.pp_qsymbol name
          (EcPrinting.pp_funname ppe) funname
          (EcPrinting.pp_funname ppe) cttfname
      )
    end;
  end

  | `Double ((_, fl, _), (_, fr, _)) ->
    let contract =
      try
        destr_equivF contract
      with DestrError _ ->
        tc_error_lazy ?loc pe (fun fmt ->
          Format.fprintf fmt
            "contract %a should be an Equiv statement"
            EcSymbols.pp_qsymbol name
        )
    in
    List.iter (fun (f, ef_f, side) ->
      if not (EcReduction.EqTest.for_xp env f ef_f) then begin
        tc_error_lazy ?loc pe (fun fmt ->
          let ppe = EcPrinting.PPEnv.ofenv env in
          Format.fprintf fmt
            "%s-side of contract %a should be for the procedure %a, not %a"
            side
            EcSymbols.pp_qsymbol name
            (EcPrinting.pp_funname ppe) f
            (EcPrinting.pp_funname ppe) ef_f
        )
      end
    ) [(fl, contract.ef_fl, "left"); (fr, contract.ef_fr, "right")]

(* -------------------------------------------------------------------- *)
let abstract_pvs
  (hyps : LDecl.hyps)
  (ms   : memory list)
  (pvs  : ((prog_var * ty) list) EcIdent.Mid.t)
=
  let env = LDecl.toenv hyps in

  let mkinv =
    match ms with
    | [m]      -> fun inv -> Inv_ss { m; inv; }
    | [ml; mr] -> fun inv -> Inv_ts { ml; mr; inv; }
    | _        -> assert false in

  let for_memory (subst : EcPV.PVM.subst) (m : memory) =
    let pvs = EcIdent.Mid.find_def [] m pvs in

    let ids = List.map (fun (pv, ty) ->
      (Format.sprintf "%s_" (EcTypes.symbol_of_pv pv)), ty) pvs in
    let ids =
      List.combine
        (LDecl.fresh_ids hyps (List.fst ids))
        (List.snd ids) in

    let pvs_as_inv = List.map (fun (pv, ty) ->
      mkinv (f_pvar pv ty m).inv
    ) pvs in
    let subst = List.fold_left (fun subst ((pv, ty), x) ->
      EcPV.PVM.add env pv m (f_local x ty) subst
    ) subst (List.combine pvs (List.fst ids)) in

    (subst, (ids, pvs, pvs_as_inv))
  in

  let subst, ids =
    List.fold_left_map for_memory EcPV.PVM.empty ms in

  let ids = List.map proj3_1 ids 
  and pvs = List.map proj3_2 ids
  and pvs_as_inv = List.map proj3_3 ids in
  let ids = List.flatten ids in
  let pvs = List.flatten pvs in
  let pvs_as_inv = List.flatten pvs_as_inv in

  ids, pvs, pvs_as_inv, subst

(* -------------------------------------------------------------------- *)
let t_ecall_hoare_fwd ((cttpt, ctt) : (proofterm * form)) (tc : tcenv1) =
  let hyps = FApi.tc1_hyps tc in
  let env = EcEnv.LDecl.toenv hyps in
  let concl = destr_hoareS (FApi.tc1_goal tc) in
  let m = (fst concl.hs_m) in
  let (lvalue, funname, _), _ = pf_first_call !!tc concl.hs_s in

  let pvs = PT.collect_pvars_from_pt cttpt in
  let ids, _, pvs_as_inv, subst = abstract_pvs hyps [m] pvs in

  let tc = t_hr_exists_intro_r pvs_as_inv tc in
  let tc = FApi.t_focus (t_hr_exists_elim_r ~bound:(List.length ids)) tc in
  let tc = FApi.t_focus (t_intros_i (List.fst ids)) tc in

  let cttpt = PT.subst_pv_pt env subst cttpt in
  let ctt = EcPV.PVM.subst env subst ctt in

  let ctt =
    EcReduction.h_red_opt EcReduction.full_red hyps ctt
    |> odfl ctt in

  let seqf =
    let inv = destr_hoareF ctt in
    let _   = assert (POE.is_empty (hf_po inv).hsi_inv) in
    let inv = POE.lower (hf_po inv) in
    let inv = ss_inv_rebind inv m in

    match lvalue with
    | None ->
      let not_contains_res (f : form) =
        let pvs = EcPV.form_read env EcPV.PMVS.empty f in
        let pvs = EcIdent.Mid.find_def EcPV.PV.empty m pvs in
        not (EcPV.PV.mem_pv env EcTypes.pv_res pvs) in
      map_ss_inv1
        (fun f -> filter_topand_form not_contains_res f |> odfl f_true)
        inv

    | Some lvalue ->
      let lv =
        List.map
          (fun (pv, ty) -> (f_pvar pv ty inv.m).inv)
          (EcModules.lv_to_ty_list lvalue) in
      let sres =
        EcPV.PVM.add
          env EcTypes.pv_res inv.m
          (f_tuple lv) EcPV.PVM.empty in

      { inv = EcPV.PVM.subst env sres inv.inv; m = inv.m; } in

  let seqf_frame =
    let wr = lvalue |> omap (EcPV.lp_write env) |> odfl EcPV.PV.empty in
    let wr = EcPV.f_write_r env wr funname in
    let inv =
      filter_topand_form
        (fun f ->
          let pvs = EcPV.form_read env EcPV.PMVS.empty f in
          let pvs = EcIdent.Mid.find_def EcPV.PV.empty m pvs in
          EcPV.PV.indep env wr pvs)
        (hs_pr concl).inv in
    { inv = odfl f_true inv; m = (hs_pr concl).m; } in

  let tc =
    FApi.t_first
      (EcPhlSeq.t_hoare_seq (GapAfter cpos1_first) (map_ss_inv2 f_and seqf seqf_frame))
      tc in

  let tc = FApi.t_first EcPhlHoare.t_hoaresplit tc in
  let tc = FApi.t_first (EcPhlConseq.t_conseqauto ~delta:false ?tsolve:None) tc in
  let tc = FApi.t_first EcPhlTAuto.t_hoare_true tc in

  let tc = FApi.t_first (EcPhlCall.t_call None ctt) tc in
  let tc = FApi.t_sub [
      EcLowGoal.Apply.t_apply_bwd_hi ~dpe:true cttpt;
      EcPhlSkip.t_skip;
      t_id
    ] tc in

  let tc =
    FApi.t_firsts
      (t_generalize_hyps ~clear:`Yes (List.fst ids)) 2 tc in

  tc

(* -------------------------------------------------------------------- *)
let t_ecall_hoare_bwd ((cttpt, _) : proofterm * form) (tc : tcenv1) =
  let hyps = FApi.tc1_hyps tc in
  let env = EcEnv.LDecl.toenv hyps in
  let concl = destr_hoareS (FApi.tc1_goal tc) in
  let m = fst (concl.hs_m) in
  let call, _ = pf_last_call !!tc concl.hs_s in

  let pvs = PT.collect_pvars_from_pt cttpt in
  let ids, _, pvs_as_inv, subst = abstract_pvs hyps [m] pvs in

  let cttpt =
    let pt_head, pt_args =
      match cttpt with
      | PTApply { pt_head; pt_args } -> (pt_head, pt_args)
      | _ -> assert false in
    let pt_args = List.map (PT.subst_pv_pt_arg env subst) pt_args in
    PTApply { pt_head; pt_args } in

  let cttpt, ctt =  EcLowGoal.LowApply.check `Elim cttpt (`Hyps (hyps, !!tc)) in

  let ctt =
    EcReduction.h_red_opt EcReduction.full_red hyps ctt
    |> odfl ctt in

  let ids_subst =
    List.fold_left2
      (fun s (id, _) pv -> EcSubst.add_flocal s id (inv_of_inv pv))
      EcSubst.empty ids pvs_as_inv in

  let fpre, fpost =
    let hf = destr_hoareF ctt in
    (ss_inv_rebind (hf_pr hf) m).inv, (hs_inv_rebind (hf_po hf) m).hsi_inv
  in

  let post =
    EcPhlCall.compute_hoare_call_post
      hyps m (fpre, fpost) call (hs_po concl).hsi_inv in
  let post = EcSubst.subst_form ids_subst post in

  let tc = EcPhlSeq.t_hoare_seq (GapBefore cpos1_last) { m = m; inv = post; } tc in
  let tc = FApi.t_last (t_hr_exists_intro_r pvs_as_inv) tc in
  let tc = FApi.t_last (t_hr_exists_elim_r ~bound:(List.length ids)) tc in
  let tc = FApi.t_last (t_intros_i (List.fst ids)) tc in
  let tc = FApi.t_last (EcPhlCall.t_call None ctt) tc in

  FApi.t_sub [
    EcLowGoal.t_id; (* initial hoare statement without the call *)
    EcLowGoal.Apply.t_apply_bwd_hi ~dpe:true cttpt; (* Prove the Hoare contract *)
    EcPhlAuto.t_auto ?conv:None; (* Kill the conseq from the call rule *)
  ] tc

(* -------------------------------------------------------------------- *)
let process_ecall_hoare
  (dir   : APT.pdirection)
  (pterm : APT.pecall)
  (tc    : tcenv1)
=
  let (ctt_path, ctt_tvi, ctt_args) = pterm in
  let hyps = FApi.tc1_hyps tc in
  let concl = destr_hoareS (FApi.tc1_goal tc) in

  (* Type-check contract (lemma) - apply it fully to find the Hoare contract *)
  let ptenv = PT.ptenv_of_penv (LDecl.push_active_ss concl.hs_m hyps) !!tc in
  let contract = PT.process_pterm ptenv (APT.FPNamed (ctt_path, ctt_tvi)) in
  let contract, _ = PT.process_pterm_args_app contract ctt_args in
  let contract = PT.apply_pterm_to_max_holes hyps contract in
  
  assert (PT.can_concretize contract.PT.ptev_env);
  let contract = PT.concretize contract in

  let call, _ =
    match dir with
    | `Forward  -> pf_first_call !!tc concl.hs_s
    | `Backward -> pf_last_call !!tc concl.hs_s in

  check_contract_type
    ~noexn:(dir <> `Backward) ~loc:(L.loc ctt_path) ~name:(L.unloc ctt_path)
    !!tc hyps (`Single call) (snd contract);

  match dir with
  | `Forward  -> t_ecall_hoare_fwd contract tc
  | `Backward -> t_ecall_hoare_bwd contract tc

(* -------------------------------------------------------------------- *)
let process_ecall_equiv
  (dir   : APT.pdirection)
  (oside : side option)
  (pterm : APT.pecall)
  (tc    : tcenv1)
=
  if dir <> `Backward then
    tc_error !!tc "unsupported direction for ecall on an equiv. goal";

  let (ctt_path, ctt_tvi, ctt_args) = pterm in
  let hyps = FApi.tc1_hyps tc in
  let env = EcEnv.LDecl.toenv hyps in
  let concl = destr_equivS (FApi.tc1_goal tc) in
  let (ml, _), (mr, _) = concl.es_ml, concl.es_mr in

  (* Type-check contract (lemma) - apply it fully to find the Hoare/Equiv contract *)
  let cttpt, _ =
    let ptenv = PT.ptenv_of_penv (LDecl.push_active_ts concl.es_ml concl.es_mr hyps) !!tc in
    let contract = PT.process_pterm ptenv (APT.FPNamed (ctt_path, ctt_tvi)) in
    let contract, _ = PT.process_pterm_args_app contract ctt_args in
    let contract = PT.apply_pterm_to_max_holes hyps contract in
    assert (PT.can_concretize contract.PT.ptev_env);
    PT.concretize contract in

  let pvs = PT.collect_pvars_from_pt cttpt in
  let ids, _, pvs_as_inv, subst = abstract_pvs hyps [ml; mr] pvs in

  let cttpt =
    let pt_head, pt_args =
      match cttpt with
      | PTApply { pt_head; pt_args } -> (pt_head, pt_args)
      | _ -> assert false in
    let pt_args = List.map (PT.subst_pv_pt_arg env subst) pt_args in
    PTApply { pt_head; pt_args } in

  let cttpt, ctt =  EcLowGoal.LowApply.check `Elim cttpt (`Hyps (hyps, !!tc)) in

  let ctt =
    EcReduction.h_red_opt EcReduction.full_red hyps ctt
    |> odfl ctt in

  let ids_subst =
    List.fold_left2
      (fun s (id, _) pv -> EcSubst.add_flocal s id (inv_of_inv pv))
      EcSubst.empty ids pvs_as_inv in

  let calls =
    match oside with
    | None ->
      let call_l, _ = pf_last_call !!tc concl.es_sl in
      let call_r, _ = pf_last_call !!tc concl.es_sr in
      `Double (call_l, call_r)
    | Some side ->
      let call, _ =
        pf_last_call !!tc (APT.sideif side concl.es_sl concl.es_sr)
      in `Single call
  in

  check_contract_type
    ~phoare:true ~loc:(L.loc ctt_path) ~name:(L.unloc ctt_path)
    !!tc hyps calls ctt;

  match calls with
  | `Single call -> begin
    let side = oget oside in
    let m = APT.sideif side ml mr in

    let fpre, fpost =
    match ctt.f_node with
    | FhoareF hf ->
      assert (POE.is_empty (hf_po hf).hsi_inv);
      (ss_inv_rebind (hf_pr hf) m).inv,
      (hs_inv_rebind (hf_po hf) m).hsi_inv.main
    | FbdHoareF hf ->
      (ss_inv_rebind (bhf_pr hf) m).inv,
      (ss_inv_rebind (bhf_po hf) m).inv
    | _ -> assert false
    in

    let post =
      EcPhlCall.compute_equiv1_call_post
        hyps side (ml, mr) (fpre, fpost) call (es_po concl).inv in
    let post = EcSubst.subst_form ids_subst post in

    let pos =
      APT.sideif side
        (GapBefore cpos1_last, GapAfter  cpos1_last)
        (GapAfter  cpos1_last, GapBefore cpos1_last) in

    let tc = EcPhlSeq.t_equiv_seq pos { ml; mr; inv = post; } tc in
    let tc = FApi.t_last (t_hr_exists_intro_r pvs_as_inv) tc in
    let tc = FApi.t_last (t_hr_exists_elim_r ~bound:(List.length ids)) tc in
    let tc = FApi.t_last (t_intros_i (List.fst ids)) tc in
    let tc = FApi.t_last (EcPhlCall.t_call (Some side) ctt) tc in

    FApi.t_sub [
      EcLowGoal.t_id; (* initial equiv statement without the call *)
      EcLowGoal.Apply.t_apply_bwd_hi ~dpe:true cttpt; (* Prove the Hoare contract *)
      EcPhlAuto.t_auto ?conv:None; (* Kill the conseq from the call rule *)
    ] tc
  end

  | `Double (call_l, call_r) -> begin
    let fpre, fpost =
      let hf = destr_equivF ctt in
      (ts_inv_rebind (ef_pr hf) ml mr).inv,
      (ts_inv_rebind (ef_po hf) ml mr).inv
    in

    let post =
      EcPhlCall.compute_equiv_call_post
        hyps (ml, mr) (fpre, fpost) call_l call_r (es_po concl).inv in
    let post = EcSubst.subst_form ids_subst post in

    let tc =
      EcPhlSeq.t_equiv_seq
        (GapBefore cpos1_last, GapBefore cpos1_last)
        { ml; mr; inv = post; } tc in

    let tc = FApi.t_last (t_hr_exists_intro_r pvs_as_inv) tc in
    let tc = FApi.t_last (t_hr_exists_elim_r ~bound:(List.length ids)) tc in
    let tc = FApi.t_last (t_intros_i (List.fst ids)) tc in
    let tc = FApi.t_last (EcPhlCall.t_call None ctt) tc in

    FApi.t_sub [
      EcLowGoal.t_id; (* initial equiv statement without the call *)
      EcLowGoal.Apply.t_apply_bwd_hi ~dpe:true cttpt; (* Prove the Hoare contract *)
      EcPhlAuto.t_auto ?conv:None; (* Kill the conseq from the call rule *)
    ] tc
  end

(* -------------------------------------------------------------------- *)
let process_ecall
  (dir   : APT.pdirection)
  (oside : side option)
  (pterm : APT.pecall) 
  (tc    : tcenv1)
=
  match (FApi.tc1_goal tc).f_node with
  | FhoareS _  ->
      if Option.is_some oside then
        tc_error !!tc "cannot provide a side for Hoare goals";
      process_ecall_hoare dir pterm tc

  | FequivS _ ->
      process_ecall_equiv dir oside pterm tc

  | _ -> tc_error_noXhl ~kinds:[`Hoare `Stmt; `Equiv `Stmt] !!tc
