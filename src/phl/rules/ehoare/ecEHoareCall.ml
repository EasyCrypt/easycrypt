(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcAst
open EcTypes
open EcFol
open EcEnv
open EcPV
open EcSubst

open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal

module PT  = EcProofTerm
module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
(* Parameters of the ehoare [call] rule: the specification of the called
   procedure. *)
type ehoare_call = {
  ehcall_pre  : ss_inv;   (* pre-expectation P of the procedure *)
  ehcall_post : ss_inv;   (* post-expectation Q of the procedure *)
}

type EcCoreGoal.rule += REHoareCall of ehoare_call

(* -------------------------------------------------------------------- *)
(* The pre- and post-expectations of [lv <@ f(a)] given the specification
   [P ==> Q] of [f] (in memory [m]): [(P[arg := a], Q[res := lv])].
   Fails with [Failure] (user-facing messages) when [lv] assigns a global
   variable, or when the call has no left-value and [Q] reads [res]. *)
let ehoare_call_pre_post env (m : memory) (n : ehoare_call) (lp, _, args) =
  let fpre  = ss_inv_rebind n.ehcall_pre  m in
  let fpost = ss_inv_rebind n.ehcall_post m in
  (* Ensure that all asigned variables are locals *)
  let all_loc =
    match lp with
    | None -> true
    | Some(LvVar (v,_)) -> EcTypes.is_loc v
    | Some(LvTuple vs) -> List.for_all (fun (v,_) -> EcTypes.is_loc v) vs in
  if not all_loc then
    failwith "ehoare call core rule: only local variables are supported on the left side of a call";
  (* The wp *)
  let fres =
    match lp with
    | None -> None
    | Some (LvVar (v,ty)) -> Some (f_pvar v ty m)
    | Some (LvTuple vs) -> Some (map_ss_inv f_tuple (List.map (fun (v,ty) -> f_pvar v ty m) vs)) in
  let wppost =
    omap_dfl (fun fres -> map_ss_inv2 (PVM.subst1 env pv_res m) fres fpost) fpost fres in
  let fv = PV.fv env m wppost.inv in
  if PV.mem_pv env pv_res fv then
    failwith
      "ehoare call core rule: the post condition of the function depend on res but the result is not assigned";

  let spre = EcPlCall.subst_args_call env m (e_tuple args) PVM.empty in
  let wppre = map_ss_inv1 (PVM.subst env spre) fpre in
  (wppre, wppost)

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. Its side conditions (the
   statement is a single call, assigning local variables only, and the pre-
   and post-expectations are the expected ones) are part of it, so the
   checker re-validates them. *)
let ehoare_call_subgoals (hyps : LDecl.hyps) (hs : eHoareS) (n : ehoare_call) =
  let env = LDecl.toenv hyps in
  let m   = fst hs.ehs_m in
  let (_, f, _) as call = EcPlCall.single_call "ehoare-call" hs.ehs_s in
  let wppre, wppost = ehoare_call_pre_post env m n call in

  let error kind expected actual =
    let env = EcEnv.Memory.push_active_ss hs.ehs_m env in
    let ppe = EcPrinting.PPEnv.ofenv env in
    failwith (Format.asprintf
      "ehoare call core rule: wrong %s-condition %a instead %a" kind
      (EcPrinting.pp_form ppe) actual (EcPrinting.pp_form ppe) expected) in

  if not (EcReduction.ss_inv_is_conv hyps (ehs_po hs) wppost) then
    error "post" wppost.inv (ehs_po hs).inv;
  if not (EcReduction.ss_inv_is_conv hyps (ehs_pr hs) wppre) then
    error "pre" wppre.inv (ehs_pr hs).inv;

  [f_eHoareF (ss_inv_rebind n.ehcall_pre m) f (ss_inv_rebind n.ehcall_post m)]

(* -------------------------------------------------------------------- *)
(* Rule (TCB). *)
let t_ehoare_call (n : ehoare_call) (tc : tcenv1) =
  let hs = tc1_as_ehoareS tc in
  let sg =
    try  ehoare_call_subgoals (FApi.tc1_hyps tc) hs n
    with Failure msg -> tc_error !!tc "%s" msg in
  FApi.xrule1 tc (REHoareCall n) sg

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | REHoareCall n ->
         Some (EcPlRecheck.checker_of "ehoare-call" pf_as_ehoareS
                 (fun hyps hs -> ehoare_call_subgoals hyps hs n))
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* The pre- and post-expectations of the last call of the goal, for the
   derived tactics (failures as tactic errors). *)
let tc1_ehoare_call_pre_post (n : ehoare_call) (tc : tcenv1) =
  let env = FApi.tc1_env tc in
  let hs  = tc1_as_ehoareS tc in
  let call, _ = tc1_last_call tc hs.ehs_s in
  try  ehoare_call_pre_post env (fst hs.ehs_m) n call
  with Failure msg -> tc_error !!tc "%s" msg

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node): on [c; lv <@ f(a)], [seq] before the call with
   its pre-expectation, then close the call with the rule. The
   specification premise comes first. *)
let t_ehoare_call_last (n : ehoare_call) (tc : tcenv1) =
  let wppre, _ = tc1_ehoare_call_pre_post n tc in
  let at = EcMatching.Position.(GapBefore cpos1_last) in
  FApi.t_swap_goals 0 1
    (FApi.t_seqsub
       (EcEHoareSeq.t_ehoare_seq { ehsr_at = at; ehsr_mid = wppre })
       [t_id; t_ehoare_call n]
       tc)

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node): as [t_ehoare_call_last], the intermediate
   pre-expectation being [fc] applied to that of the call, and the call
   being reduced to the rule by the concave consequence.
   TEMPORARY: the concave consequence comes from the not-yet-migrated
   [EcPhlConseq]. *)
let t_ehoare_call_concave (fc : ss_inv) (n : ehoare_call) (tc : tcenv1) =
  let wppre, wppost = tc1_ehoare_call_pre_post n tc in
  let at  = EcMatching.Position.(GapBefore cpos1_last) in
  let mid = map_ss_inv2 (fun wppre f -> f_app_simpl f [wppre] txreal) wppre fc in
  let t_call =
    FApi.t_seqsub (EcPhlConseq.t_ehoareS_concave fc wppre wppost)
      [t_id; t_id; t_id; t_ehoare_call n] in
  FApi.t_sub [t_call; t_id]
    (FApi.t_swap_goals 0 1
       (EcEHoareSeq.t_ehoare_seq { ehsr_at = at; ehsr_mid = mid } tc))

(* -------------------------------------------------------------------- *)
(* Elaboration: the goal is known to be an [eHoareS]. Types the cut of
   [call]: the specification of the last call. *)
let process_ehoare_call_cut (side : oside) (info : call_info) (tc : tcenv1) =
  let hyps, concl = FApi.tc1_flat tc in
  let hs = destr_eHoareS concl in
  let last_f () = proj3_2 (fst (tc1_last_call tc hs.ehs_s)) in

  match info with
  | CI_spec (pre, epost) ->
    if not (is_none side) then
      tc_error !!tc "the conclusion is not a hoare or an equiv";
    let f = last_f () in
    let m = EcIdent.create "&hr" in
    let penv, qenv = LDecl.hoareF m f hyps in
    let pre  = TTC.pf_process_form !!tc penv txreal pre  in
    let post = TTC.pf_process_form !!tc qenv txreal epost.pnormal in
    (f_eHoareF {m;inv=pre} f {m;inv=post}, t_id)

  | CI_inv inv ->
    if not (is_none side) then
      tc_error !!tc "cannot specify side for call with invariants";
    let m    = fst hs.ehs_m in
    let f    = last_f () in
    let hyps = LDecl.push_active_ss (EcMemory.abstract m) hyps in
    let inv  = TTC.pf_process_form !!tc hyps txreal inv in
    let inv  = {m; inv} in
    let t_spec tc =
      FApi.t_firsts t_trivial 2 (EcPhlFun.t_fun (Inv_ss inv) tc) in
    (f_eHoareF inv f inv, t_spec)

  | CI_upto _ ->
    if not (is_none side) then
      tc_error !!tc "cannot specify side for call with invariants";
    tc_error !!tc "the conclusion is not an equiv"

(* -------------------------------------------------------------------- *)
(* Elaboration: [call /fc (spec)], the goal being known to be an
   [eHoareS]. *)
let process_ehoare_call_concave (fc, info) tc =
  let fc =
    let hs  = tc1_as_ehoareS tc in
    let env = LDecl.push_active_ss hs.ehs_m (FApi.tc1_hyps tc) in
    {m=fst hs.ehs_m;inv=TTC.pf_process_form !!tc env (tfun txreal txreal) fc} in

  let subtactic = ref t_id in

  (* As for [call] ([process_ehoare_call_cut]), the specification is typed
     in the memories of the called procedure and the invariant in an
     abstract memory: the local variables of the caller are not in
     scope. *)
  let process_cut tc info =
    match info with
    | CI_spec _ ->
      fst (process_ehoare_call_cut None info tc)

    | CI_inv _ ->
      let spec, t_spec = process_ehoare_call_cut None info tc in
      subtactic := t_spec;
      spec

    | _ ->
        tc_error !!tc "cannot supply additional information for call /"

  in

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

  let t_call ax tc =
    let env = FApi.tc1_env tc in
    let hs  = tc1_as_ehoareS tc in
    match ax.f_node with
    | FeHoareF hf ->
      let (_, f, _), _ = tc1_last_call tc hs.ehs_s in
      if not (EcEnv.NormMp.x_equal env hf.ehf_f f) then
        EcPlCall.call_error env tc hf.ehf_f f;
      t_ehoare_call_concave fc
        { ehcall_pre = ehf_pr hf; ehcall_post = ehf_po hf; } tc
    | _ -> tc_error !!tc "call: invalid goal shape" in

  FApi.t_seqsub
    (t_call ax)
    [ EcPhlConseq.t_concave_incr;
      t_trivial; (* pre *)
      t_trivial; (* post *)
      FApi.t_seqs
        [EcLowGoal.Apply.t_apply_bwd_hi ~dpe:true pt;
         !subtactic; t_trivial];
      t_id]
    tc
