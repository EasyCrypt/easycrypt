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
(* The exists rules, quantifying the precondition over the values of the
   program variables [pvs] of memories [ml] / [mr] and introducing them as
   [ids]. *)
let t_abstract_pvs
  ((ml, mr) : memory * memory)
  (ids      : (EcIdent.t * ty) list)
  (pvs      : form list)
=
  FApi.t_seqs [
    EcEquivExists.t_equiv_exists_intro
      (List.map (fun inv -> { ml; mr; inv }) pvs);
    EcEquivExists.t_equivS_exists_elim
      { exe_bound = Some (List.length ids) };
    t_intros_i (List.fst ids);
  ]

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node). *)
let t_equiv_ecall_onesided
  (side         : APT.side)
  ((cttpt, ctt) : proofterm * form)
  ((ids, pvs)   : (EcIdent.t * ty) list * form list)
  (call         : EcPlECall.call)
  (tc           : tcenv1)
=
  let hyps = FApi.tc1_hyps tc in
  let es   = tc1_as_equivS tc in
  let (ml, _), (mr, _) = es.es_ml, es.es_mr in
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

  let mid =
    EcEquivCall.equiv_call_onesided_wp
      hyps side (ml, mr) (fpre, fpost) call (es_po es).inv in
  let mid = EcSubst.subst_form (EcPlECall.restore_pvs ids pvs) mid in

  (* The call rule, as [call{side}] applies it: the one-sided rule takes a
     phoare specification. *)
  let t_call (tc : tcenv1) =
    match ctt.f_node with
    | FbdHoareF hf ->
        EcEquivCall.(t_equiv_call_onesided_last
          { ecallos_side = side;
            ecallos_pre  = bhf_pr hf;
            ecallos_post = bhf_po hf; }) tc
    | _ -> tc_error !!tc "call: invalid goal shape" in

  let at =
    APT.sideif side
      (GapBefore cpos1_last, GapAfter  cpos1_last)
      (GapAfter  cpos1_last, GapBefore cpos1_last) in

  let tc =
    EcEquivSeq.t_equiv_seq
      { esr_at = at; esr_mid = { ml; mr; inv = mid; }; } tc in
  let tc = FApi.t_last (t_abstract_pvs (ml, mr) ids pvs) tc in
  let tc = FApi.t_last t_call tc in

  FApi.t_sub [
    t_id;                                  (* the prefixes *)
    Apply.t_apply_bwd_hi ~dpe:true cttpt;  (* the contract *)
    EcPhlAuto.t_auto ?conv:None;           (* the skips before the calls *)
  ] tc

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node). *)
let t_equiv_ecall
  ((cttpt, ctt)     : proofterm * form)
  ((ids, pvs)       : (EcIdent.t * ty) list * form list)
  ((call_l, call_r) : EcPlECall.call * EcPlECall.call)
  (tc               : tcenv1)
=
  let hyps = FApi.tc1_hyps tc in
  let es   = tc1_as_equivS tc in
  let (ml, _), (mr, _) = es.es_ml, es.es_mr in

  let ef = destr_equivF ctt in
  let fpre, fpost =
    (ts_inv_rebind (ef_pr ef) ml mr).inv,
    (ts_inv_rebind (ef_po ef) ml mr).inv
  in

  let mid =
    EcEquivCall.equiv_call_wp
      hyps (ml, mr) (fpre, fpost) call_l call_r (es_po es).inv in
  let mid = EcSubst.subst_form (EcPlECall.restore_pvs ids pvs) mid in

  let tc =
    EcEquivSeq.t_equiv_seq
      { esr_at  = (GapBefore cpos1_last, GapBefore cpos1_last);
        esr_mid = { ml; mr; inv = mid; }; } tc in
  let tc = FApi.t_last (t_abstract_pvs (ml, mr) ids pvs) tc in
  let tc =
    FApi.t_last
      EcEquivCall.(t_equiv_call_last
        { ecall_pre = ef_pr ef; ecall_post = ef_po ef; })
      tc in

  FApi.t_sub [
    t_id;                                  (* the prefixes *)
    Apply.t_apply_bwd_hi ~dpe:true cttpt;  (* the contract *)
    EcPhlAuto.t_auto ?conv:None;           (* the skips before the calls *)
  ] tc

(* -------------------------------------------------------------------- *)
(* Elaboration: the goal is known to be an [equivS]. *)
let process_equiv_ecall
  (dir   : APT.pdirection)
  (oside : APT.oside)
  (pterm : APT.pecall)
  (tc    : tcenv1)
=
  if dir <> `Backward then
    tc_error !!tc "unsupported direction for ecall on an equiv. goal";

  let (ctt_path, _, _) = pterm in
  let hyps = FApi.tc1_hyps tc in
  let env  = LDecl.toenv hyps in
  let es   = tc1_as_equivS tc in
  let (ml, _), (mr, _) = es.es_ml, es.es_mr in

  let cttpt, _ =
    EcPlECall.process_contract
      !!tc (LDecl.push_active_ts es.es_ml es.es_mr hyps) hyps pterm in

  let pvs = PT.collect_pvars_from_pt cttpt in
  let ids, pvs, subst = EcPlECall.abstract_pvs hyps [ml; mr] pvs in

  let cttpt = EcPlECall.subst_pt_args env subst cttpt in
  let cttpt, ctt = LowApply.check `Elim cttpt (`Hyps (hyps, !!tc)) in

  let ctt =
    EcReduction.h_red_opt EcReduction.full_red hyps ctt
    |> odfl ctt in

  let calls =
    match oside with
    | None ->
      let call_l, _ = pf_last_call !!tc es.es_sl in
      let call_r, _ = pf_last_call !!tc es.es_sr in
      `Double (call_l, call_r)
    | Some side ->
      let call, _ = pf_last_call !!tc (APT.sideif side es.es_sl es.es_sr) in
      `Single call
  in

  EcPlECall.check_contract_type
    ~phoare:true ~loc:(L.loc ctt_path) ~name:(L.unloc ctt_path)
    !!tc hyps calls ctt;

  match calls with
  | `Single call ->
      t_equiv_ecall_onesided (oget oside) (cttpt, ctt) (ids, pvs) call tc
  | `Double calls ->
      t_equiv_ecall (cttpt, ctt) (ids, pvs) calls tc
