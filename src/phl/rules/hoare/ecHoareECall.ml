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
module PT  = EcProofTerm

(* -------------------------------------------------------------------- *)
(* The call rule, as [call] applies it, for the contract [ctt]. *)
let t_call (ctt : form) =
  let hf = destr_hoareF ctt in
  EcHoareCall.(t_hoare_call_last
    { hcall_pre = hf_pr hf; hcall_post = hf_po hf; })

(* The exists rules, quantifying the precondition over the values of the
   program variables [pvs] of memory [m] and introducing them as [ids]. *)
let t_abstract_pvs
  (m   : memory)
  (ids : (EcIdent.t * ty) list)
  (pvs : form list)
=
  FApi.t_seqs [
    EcHoareExists.t_hoare_exists_intro
      (List.map (fun inv -> { m; inv }) pvs);
    EcHoareExists.t_hoareS_exists_elim
      { hxe_bound = Some (List.length ids) };
    t_intros_i (List.fst ids);
  ]

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node). *)
let t_hoare_ecall_fwd ((cttpt, ctt) : proofterm * form) (tc : tcenv1) =
  let hyps = FApi.tc1_hyps tc in
  let env  = LDecl.toenv hyps in
  let hs   = tc1_as_hoareS tc in
  let m    = fst hs.hs_m in
  let (lvalue, funname, _), _ = pf_first_call !!tc hs.hs_s in

  let pvs = PT.collect_pvars_from_pt cttpt in
  let ids, pvs, subst = EcPlECall.abstract_pvs hyps [m] pvs in

  let tc = t_abstract_pvs m ids pvs tc in

  let cttpt = PT.subst_pv_pt env subst cttpt in
  let ctt = EcPV.PVM.subst env subst ctt in

  let ctt =
    EcReduction.h_red_opt EcReduction.full_red hyps ctt
    |> odfl ctt in

  (* The postcondition of the contract, its result assigned to [lvalue]
     (or its conjuncts mentioning [res] dropped when there is none). *)
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

  (* The conjuncts of the precondition independent of the variables
     written by the call. *)
  let seqf_frame =
    let wr = lvalue |> omap (EcPV.lp_write env) |> odfl EcPV.PV.empty in
    let wr = EcPV.f_write_r env wr funname in
    let inv =
      filter_topand_form
        (fun f ->
          let pvs = EcPV.form_read env EcPV.PMVS.empty f in
          let pvs = EcIdent.Mid.find_def EcPV.PV.empty m pvs in
          EcPV.PV.indep env wr pvs)
        (hs_pr hs).inv in
    { inv = odfl f_true inv; m = (hs_pr hs).m; } in

  let tc =
    FApi.t_first
      (EcHoareSeq.t_hoare_seq
         { hsr_at  = GapAfter cpos1_first;
           hsr_mid = map_ss_inv2 f_and seqf seqf_frame; })
      tc in

  let tc = FApi.t_first EcHoareSplit.t_hoare_split tc in
  (* TEMPORARY: the automated framed consequence still comes from the
     not-yet-migrated [EcPhlConseq] (its framing is the frame rule). *)
  let tc =
    FApi.t_first (EcPhlConseq.t_conseqauto ~delta:false ?tsolve:None) tc in
  let tc = FApi.t_first EcHoareTrue.t_hoare_true tc in

  let tc = FApi.t_first (t_call ctt) tc in
  let tc = FApi.t_sub [
      Apply.t_apply_bwd_hi ~dpe:true cttpt;
      EcHoareSkip.t_hoare_skip;
      t_id
    ] tc in

  FApi.t_firsts (t_generalize_hyps ~clear:`Yes (List.fst ids)) 2 tc

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node). *)
let t_hoare_ecall_bwd ((cttpt, _) : proofterm * form) (tc : tcenv1) =
  let hyps = FApi.tc1_hyps tc in
  let env  = LDecl.toenv hyps in
  let hs   = tc1_as_hoareS tc in
  let m    = fst hs.hs_m in
  let call, _ = pf_last_call !!tc hs.hs_s in

  let pvs = PT.collect_pvars_from_pt cttpt in
  let ids, pvs, subst = EcPlECall.abstract_pvs hyps [m] pvs in

  let cttpt = EcPlECall.subst_pt_args env subst cttpt in
  let cttpt, ctt = LowApply.check `Elim cttpt (`Hyps (hyps, !!tc)) in

  let ctt =
    EcReduction.h_red_opt EcReduction.full_red hyps ctt
    |> odfl ctt in

  let fpre, fpost =
    let hf = destr_hoareF ctt in
    (ss_inv_rebind (hf_pr hf) m).inv, (hs_inv_rebind (hf_po hf) m).hsi_inv
  in

  let mid =
    EcHoareCall.hoare_call_wp hyps m (fpre, fpost) call (hs_po hs).hsi_inv in
  let mid = EcSubst.subst_form (EcPlECall.restore_pvs ids pvs) mid in

  let tc =
    EcHoareSeq.t_hoare_seq
      { hsr_at = GapBefore cpos1_last; hsr_mid = { m; inv = mid; }; } tc in
  let tc = FApi.t_last (t_abstract_pvs m ids pvs) tc in
  let tc = FApi.t_last (t_call ctt) tc in

  FApi.t_sub [
    t_id;                                  (* the prefix *)
    Apply.t_apply_bwd_hi ~dpe:true cttpt;  (* the contract *)
    EcPhlAuto.t_auto ?conv:None;           (* the skip before the call *)
  ] tc

(* -------------------------------------------------------------------- *)
(* Elaboration: the goal is known to be a [hoareS]. *)
let process_hoare_ecall
  (dir   : APT.pdirection)
  (oside : APT.oside)
  (pterm : APT.pecall)
  (tc    : tcenv1)
=
  if Option.is_some oside then
    tc_error !!tc "cannot provide a side for Hoare goals";

  let (ctt_path, _, _) = pterm in
  let hyps = FApi.tc1_hyps tc in
  let hs = tc1_as_hoareS tc in

  let contract =
    EcPlECall.process_contract
      !!tc (LDecl.push_active_ss hs.hs_m hyps) hyps pterm in

  let call, _ =
    match dir with
    | `Forward  -> pf_first_call !!tc hs.hs_s
    | `Backward -> pf_last_call !!tc hs.hs_s in

  EcPlECall.check_contract_type
    ~noexn:(dir <> `Backward) ~loc:(L.loc ctt_path) ~name:(L.unloc ctt_path)
    !!tc hyps (`Single call) (snd contract);

  match dir with
  | `Forward  -> t_hoare_ecall_fwd contract tc
  | `Backward -> t_hoare_ecall_bwd contract tc
