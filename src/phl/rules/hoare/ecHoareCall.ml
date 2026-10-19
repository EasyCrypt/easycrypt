(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcAst
open EcTypes
open EcModules
open EcFol
open EcEnv
open EcPV
open EcSubst

open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal

module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
(* Parameters of the hoare [call] rule: the specification of the called
   procedure. *)
type hoare_call = {
  hcall_pre  : ss_inv;   (* precondition P of the procedure *)
  hcall_post : hs_inv;   (* postcondition Q | E_f of the procedure *)
}

type EcCoreGoal.rule += RHoareCall of hoare_call

(* -------------------------------------------------------------------- *)
(* Weakest precondition of [lv <@ f(a)] for the postcondition [post],
   given the specification [P ==> Q | E_f] of [f] (in memory [m]):
     P[arg := a] /\ forall result, forall (mod f), Q[res := result] => post[lv := result]
   conjoined with, for each exception [e], [forall (mod f), E_f(e) => E(e)]. *)
let hoare_call_wp
  (hyps     : LDecl.hyps)
  (m        : memory)
  (contract : form * exnpost)
  (call     : lvalue option * EcPath.xpath * expr list)
  (post     : exnpost)
=
  let env = LDecl.toenv hyps in

  let (fpre, fpost) = contract in
  let (lvalue, funname, funargs) = call in
  let funsig = (Fun.by_xpath funname env).f_sig in
  let modi  = f_write env funname in

  let { main = fpost; exnmap = fepost; } = fpost in
  let { main = post ; exnmap =  epost; } =  post in

  let vres = LDecl.fresh_id hyps "result" in
  let fres = f_local vres funsig.fs_ret in

  let fpost = PVM.subst1 env pv_res m fres fpost in

  let post =
    EcPlCall.wp_asgn_call env lvalue { m = m; inv = fres; } { m = m; inv = post; } in
  let post = (ss_inv_rebind post m).inv in
  let post = f_imp_simpl fpost post in
  let post = generalize_mod_ss_inv env modi { m = m; inv = post; } in
  let post = (ss_inv_rebind post m).inv in
  let post = f_forall_simpl [(vres, GTty funsig.fs_ret)] post in
  let post =
    let spre = EcPlCall.subst_args_call env m (e_tuple funargs) PVM.empty in
    f_anda_simpl (PVM.subst env spre fpre) post in

  let poe = TTC.merge2_poe_list epost fepost in
  let poe = List.map (fun inv -> { m; inv; }) poe in
  let poe =
    let penv_e = EcEnv.Fun.inv_memenv1 m env in
    List.map (fun f ->
      let genf = generalize_mod_ss_inv penv_e modi f in
      (ss_inv_rebind genf m).inv
    ) poe in

  List.fold f_anda_simpl post poe

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. Its side conditions (the
   statement is a single call, the precondition is its weakest
   precondition) are part of it, so the checker re-validates them. *)
let hoare_call_subgoals (hyps : LDecl.hyps) (hs : sHoareS) (n : hoare_call) =
  let m     = fst hs.hs_m in
  let fpre  = ss_inv_rebind n.hcall_pre m in
  let fpost = hs_inv_rebind n.hcall_post m in
  let (_, f, _) as call = EcPlCall.single_call "hoare-call" hs.hs_s in
  let wp =
    hoare_call_wp hyps m (fpre.inv, fpost.hsi_inv) call (hs_po hs).hsi_inv in
  if not (EcReduction.is_conv hyps (hs_pr hs).inv wp) then
    failwith "hoare-call: the precondition is not the expected one";
  [f_hoareF fpre f fpost]

(* -------------------------------------------------------------------- *)
(* Rule (TCB). *)
let t_hoare_call (n : hoare_call) (tc : tcenv1) =
  let hs = tc1_as_hoareS tc in
  let sg =
    try  hoare_call_subgoals (FApi.tc1_hyps tc) hs n
    with Failure msg -> tc_error !!tc "%s" msg in
  FApi.xrule1 tc (RHoareCall n) sg

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | RHoareCall n ->
         Some (EcPlRecheck.checker_of "hoare-call" pf_as_hoareS
                 (fun hyps hs -> hoare_call_subgoals hyps hs n))
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node): on [c; lv <@ f(a)], [seq] before the call with
   its weakest precondition as intermediate assertion, then close the call
   with the rule. The specification premise comes first. *)
let t_hoare_call_last (n : hoare_call) (tc : tcenv1) =
  let hyps  = FApi.tc1_hyps tc in
  let hs    = tc1_as_hoareS tc in
  let m     = fst hs.hs_m in
  let fpre  = ss_inv_rebind n.hcall_pre m in
  let fpost = hs_inv_rebind n.hcall_post m in
  let call, _ = tc1_last_call tc hs.hs_s in
  let mid =
    hoare_call_wp hyps m (fpre.inv, fpost.hsi_inv) call (hs_po hs).hsi_inv in
  let at  = EcMatching.Position.gap_before_last_n 1 in
  FApi.t_swap_goals 0 1
    (FApi.t_seqsub
       (EcHoareSeq.t_hoare_seq { hsr_at = at; hsr_mid = { m; inv = mid; } })
       [t_id; t_hoare_call n]
       tc)

(* -------------------------------------------------------------------- *)
(* Elaboration: the goal is known to be a [hoareS]. Types the cut of
   [call]: the specification of the last call. *)
let process_hoare_call_cut (side : oside) (info : call_info) (tc : tcenv1) =
  let hyps, concl = FApi.tc1_flat tc in
  let hs = destr_hoareS concl in
  let last_f () = proj3_2 (fst (tc1_last_call tc hs.hs_s)) in

  match info with
  | CI_spec (pre, epost) ->
    if not (is_none side) then
      tc_error !!tc "the conclusion is not a hoare";
    let f = last_f () in
    let m = EcIdent.create "&hr" in
    let penv, qenv = LDecl.hoareF m f hyps in
    let pre  = TTC.pf_process_form !!tc penv tbool pre  in
    let post = TTC.pf_process_form !!tc qenv tbool epost.pnormal in
    let env_e = LDecl.inv_memenv1 m hyps in
    let poe = TTC.pf_process_poe env_e epost.pexcept in
    let spec =
      f_hoareF {m; inv = pre} f
        { hsi_m = m; hsi_inv = { main = post; exnmap = poe; } } in
    (spec, t_id)

  | CI_inv inv ->
    if not (is_none side) then
      tc_error !!tc "cannot specify side for call with invariants";
    let m    = fst hs.hs_m in
    let f    = last_f () in
    let hyps = LDecl.push_active_ss (EcMemory.abstract m) hyps in
    let inv  = TTC.pf_process_form !!tc hyps tbool inv in
    let inv  = {m; inv} in
    let t_spec tc =
      FApi.t_firsts t_trivial 2 (EcPhlFun.t_fun (Inv_ss inv) tc) in
    (f_hoareF inv f (POE.lift inv), t_spec)

  | CI_upto _ ->
    if not (is_none side) then
      tc_error !!tc "cannot specify side for call with invariants";
    tc_error !!tc "the conclusion is not an equiv"
