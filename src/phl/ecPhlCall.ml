(* -------------------------------------------------------------------- *)
open EcParsetree
open EcAst

open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal

module PT  = EcProofTerm
module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
(* The [call] rules live, one module per logic, in [rules/<logic>/]:
   [EcHoareCall], [EcEHoareCall], [EcBdHoareCall] and [EcEquivCall] (two-
   and one-sided); their shared computations are in [EcPlCall]. This
   module only keeps the legacy entry points (adapters onto those rules,
   so external callers and this module's interface are unchanged) and the
   logic-agnostic dispatchers. *)

(* -------------------------------------------------------------------- *)
let compute_hoare_call_post = EcHoareCall.hoare_call_wp

let compute_equiv_call_post = EcEquivCall.equiv_call_wp

let compute_equiv1_call_post = EcEquivCall.equiv_call_onesided_wp

(* -------------------------------------------------------------------- *)
let t_hoare_call fpre fpost =
  EcHoareCall.(t_hoare_call_last { hcall_pre = fpre; hcall_post = fpost; })

let t_ehoare_call fpre fpost =
  EcEHoareCall.(t_ehoare_call_last { ehcall_pre = fpre; ehcall_post = fpost; })

let t_bdhoare_call fpre fpost opt_bd =
  EcBdHoareCall.(t_bdhoare_call
    { bhcall_pre = fpre; bhcall_post = fpost; bhcall_bd = opt_bd; })

let t_equiv_call fpre fpost =
  EcEquivCall.(t_equiv_call_last { ecall_pre = fpre; ecall_post = fpost; })

let t_equiv_call1 side fpre fpost =
  EcEquivCall.(t_equiv_call_onesided_last
    { ecallos_side = side; ecallos_pre = fpre; ecallos_post = fpost; })

(* -------------------------------------------------------------------- *)
(* Dispatch on the specification [ax] and the goal. *)
let t_call side ax tc =
  let env   = FApi.tc1_env  tc in
  let hyps, concl = FApi.tc1_flat tc in
  let ax = EcReduction.h_red_until EcReduction.full_red hyps ax in
  match ax.f_node, concl.f_node with
  | FhoareF hf, FhoareS hs ->
      let (_, f, _), _ = tc1_last_call tc hs.hs_s in
      if not (EcEnv.NormMp.x_equal env hf.hf_f f) then
        EcPlCall.call_error env tc hf.hf_f f;
      t_hoare_call (hf_pr hf) (hf_po hf) tc

  | FeHoareF hf, FeHoareS hs ->
      let (_, f, _), _ = tc1_last_call tc hs.ehs_s in
      if not (EcEnv.NormMp.x_equal env hf.ehf_f f) then
        EcPlCall.call_error env tc hf.ehf_f f;
      t_ehoare_call (ehf_pr hf) (ehf_po hf) tc

  | FbdHoareF hf, FbdHoareS hs ->
      let (_, f, _), _ = tc1_last_call tc hs.bhs_s in
      if not (EcEnv.NormMp.x_equal env hf.bhf_f f) then
        EcPlCall.call_error env tc hf.bhf_f f;
      t_bdhoare_call (bhf_pr hf) (bhf_po hf) None tc

  | FequivF ef, FequivS es ->
      let (_, fl, _), _ = tc1_last_call tc es.es_sl in
      let (_, fr, _), _ = tc1_last_call tc es.es_sr in
      if not (EcEnv.NormMp.x_equal env ef.ef_fl fl) ||
         not (EcEnv.NormMp.x_equal env ef.ef_fr fr) then
        tc_error_lazy !!tc (fun fmt ->
          let ppe = EcPrinting.PPEnv.ofenv env in
            Format.fprintf fmt
              "call cannot be used with a lemma referring to `%a/%a': \
               the last statement is a call to `%a/%a'"
              (EcPrinting.pp_funname ppe) ef.ef_fl
              (EcPrinting.pp_funname ppe) ef.ef_fr
              (EcPrinting.pp_funname ppe) fl
              (EcPrinting.pp_funname ppe) fr);
      t_equiv_call (ef_pr ef) (ef_po ef) tc

  | FbdHoareF hf, FequivS _ ->
      let side =
        match side with
        | None -> tc_error !!tc "call: a side {1|2} should be provided"
        | Some side -> side
      in
        t_equiv_call1 side (bhf_pr hf) (bhf_po hf) tc

  | _, _ -> tc_error !!tc "call: invalid goal shape"

(* -------------------------------------------------------------------- *)
(* Dispatch the typing of the cut (the specification of the called
   procedure) on the goal. *)
let process_call_cut side tc info =
  match (FApi.tc1_goal tc).f_node, info with
  | FhoareS   _, _ -> EcHoareCall.process_hoare_call_cut side info tc
  | FeHoareS  _, _ -> EcEHoareCall.process_ehoare_call_cut side info tc
  | FbdHoareS _, _ -> EcBdHoareCall.process_bdhoare_call_cut side info tc
  | FequivS   _, _ -> EcEquivCall.process_equiv_call_cut side info tc

  | _, CI_spec _ ->
      tc_error !!tc "the conclusion is not a hoare or an equiv"

  | _, CI_inv _ ->
      if not (Option.is_none side) then
        tc_error !!tc "cannot specify side for call with invariants";
      tc_error !!tc "the conclusion is not a hoare or an equiv"

  | _, CI_upto _ ->
      if not (Option.is_none side) then
        tc_error !!tc "cannot specify side for call with invariants";
      tc_error !!tc "the conclusion is not an equiv"

(* -------------------------------------------------------------------- *)
let process_call (side, info) tc =
  let subtactic = ref t_id in

  let process_cut tc info =
    let spec, t_spec = process_call_cut side tc info in
    subtactic := t_spec; spec in

  let pt = PT.tc1_process_full_pterm_cut ~prcut:(process_cut tc) tc info
  in

  let pt =
    let rec doit pt =
      match TTC.destruct_product ~reduce:true (FApi.tc1_hyps tc) pt.PT.ptev_ax with
      | None   -> pt
      | Some _ -> doit (EcProofTerm.apply_pterm_to_hole pt)
    in doit pt in

  let pt, ax =
    if not (PT.can_concretize pt.PT.ptev_env) then
      tc_error !!tc "cannot infer all placeholders";
    PT.concretize pt in

  FApi.t_seqsub
    (t_call side ax)
    [FApi.t_seqs
       [EcLowGoal.Apply.t_apply_bwd_hi ~dpe:true pt;
        !subtactic; t_trivial];
     t_id]
    tc

(* -------------------------------------------------------------------- *)
let process_call_concave (fc, info) tc =
  match (FApi.tc1_goal tc).f_node with
  | FeHoareS _ -> EcEHoareCall.process_ehoare_call_concave (fc, info) tc
  | _ -> tc_error !!tc "the conclusion is not a ehoare"
