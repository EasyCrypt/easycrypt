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
(* Derived (no proof-node). *)
let t_bdhoare_ecall_bwd ((cttpt, _) : proofterm * form) (tc : tcenv1) =
  let hyps = FApi.tc1_hyps tc in
  let env  = LDecl.toenv hyps in
  let bhs  = tc1_as_bdhoareS tc in
  let m    = fst bhs.bhs_m in
  let call, _ = pf_last_call !!tc bhs.bhs_s in

  (* The trivial probability split below (f1 = f2 = 1, g1 = g2 = 0) only
     discharges the bound side conditions when the goal is [= 1%r]. *)
  if bhs.bhs_cmp <> FHeq || not (f_equal (bhs_bd bhs).inv f_r1) then
    tc_error !!tc
      "backward ecall on phoare goals is only supported for lossless `= 1%%r' goals";

  let pvs = PT.collect_pvars_from_pt cttpt in
  let ids, pvs, subst = EcPlECall.abstract_pvs hyps [m] pvs in

  let cttpt = EcPlECall.subst_pt_args env subst cttpt in
  let cttpt, ctt = LowApply.check `Elim cttpt (`Hyps (hyps, !!tc)) in

  let ctt =
    EcReduction.h_red_opt EcReduction.full_red hyps ctt
    |> odfl ctt in

  let hf = destr_bdHoareF ctt in

  (* The suffix is given the bound [= 1%r]: only a lossless contract
     applies to it. *)
  if hf.bhf_cmp <> FHeq || not (f_equal (bhf_bd hf).inv f_r1) then
    tc_error !!tc
      "backward ecall on phoare goals requires a lossless `= 1%%r' contract";

  let fpre, fpost =
    (ss_inv_rebind (bhf_pr hf) m).inv, (ss_inv_rebind (bhf_po hf) m).inv
  in

  let mid =
    EcHoareCall.hoare_call_wp
      hyps m (fpre, POE.empty fpost) call
      (POE.empty (bhs_po bhs).inv) in
  let mid = EcSubst.subst_form (EcPlECall.restore_pvs ids pvs) mid in

  (* [seq] before the call, with the trivial split
     [phi = mid, R = true, f1 = f2 = 1%r, g1 = g2 = 0%r]: premises
     (H) hoare [c : P ==> mid], (F1) phoare [c : P ==> true] = 1%r,
     (F2) phoare [lv <@ f(a) : mid /\ true ==> Q] = 1%r,
     (G1) phoare [c : P ==> false] = 0%r, (B), and (N) when not closed. *)
  let tc =
    EcBdHoareSeq.t_bdhoare_seq_full
      { bsr_at  = GapBefore cpos1_last;
        bsr_phi = { m; inv = mid  };
        bsr_r   = { m; inv = f_true };
        bsr_f1  = { m; inv = f_r1 };
        bsr_f2  = { m; inv = f_r1 };
        bsr_g1  = { m; inv = f_r0 };
        bsr_g2  = { m; inv = f_r0 }; }
      tc in

  (* (F2): the exists rules, abstracting the program variables of the
     contract, then the call rule. *)
  let t_suffix =
    FApi.t_seqs [
      EcBdHoareExists.t_bdhoare_exists_intro
        (List.map (fun inv -> { m; inv }) pvs);
      EcBdHoareExists.t_bdhoareS_exists_elim
        { bxe_bound = Some (List.length ids) };
      t_intros_i (List.fst ids);
      FApi.t_seqsub
        (EcBdHoareCall.t_bdhoare_call
           { bhcall_pre = bhf_pr hf; bhcall_post = bhf_po hf;
             bhcall_bd = None; })
        [ Apply.t_apply_bwd_hi ~dpe:true cttpt;
          EcPhlAuto.t_auto ?conv:None; ];
    ]
  in

  (* (H) is lifted to [phoare [c : P ==> mid] = 1%r], so that further
     [ecall]s on it are on a phoare goal (the prefix must then be proved
     lossless); (F2) as above; the other premises (the count of which
     depends on whether (N) was closed) by [auto].

     TEMPORARY: the lifting still comes from the not-yet-migrated
     [EcPhlConseq]. *)
  FApi.t_onalli
    (fun i ->
      if i = 0 then EcPhlConseq.t_hoareS_conseq_bdhoare
      else if i = 2 then t_suffix
      else EcPhlAuto.t_auto ?conv:None)
    tc

(* -------------------------------------------------------------------- *)
(* Elaboration: the goal is known to be a [bdHoareS]. *)
let process_bdhoare_ecall
  (dir   : APT.pdirection)
  (oside : APT.oside)
  (pterm : APT.pecall)
  (tc    : tcenv1)
=
  if Option.is_some oside then
    tc_error !!tc "cannot provide a side for bdHoare/phoare goals";

  if dir <> `Backward then
    tc_error !!tc "forward ecall on bdHoare/phoare goals is not supported";

  let (ctt_path, _, _) = pterm in
  let hyps = FApi.tc1_hyps tc in
  let bhs = tc1_as_bdhoareS tc in

  let contract =
    EcPlECall.process_contract
      !!tc (LDecl.push_active_ss bhs.bhs_m hyps) hyps pterm in

  let call, _ = pf_last_call !!tc bhs.bhs_s in

  EcPlECall.check_contract_type
    ~phoare:true ~noexn:false ~loc:(L.loc ctt_path) ~name:(L.unloc ctt_path)
    !!tc hyps (`Single call) (snd contract);

  t_bdhoare_ecall_bwd contract tc
