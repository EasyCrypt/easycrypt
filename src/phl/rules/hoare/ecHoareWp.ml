(* -------------------------------------------------------------------- *)
open EcUtils
open EcAst
open EcEnv

open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* Parameter of the hoare [wp] rule: whether the weakest precondition
   let-binds its substitutions. Nothing to resolve: the same record is the
   rule argument and the node payload. *)
type hoare_wp = {
  hwp_uselet : bool;
}

type EcCoreGoal.rule += RHoareWp of hoare_wp

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. The rule has no premise;
   its side conditions (the statement is entirely wp-able, the
   precondition is its weakest precondition) are part of it, so the
   checker re-validates them. *)
let hoare_wp_subgoals (hyps : LDecl.hyps) (hs : sHoareS) (n : hoare_wp) =
  let r, pre =
    EcPlWp.wp ~uselet:n.hwp_uselet ~onesided:true
      hyps hs.hs_m hs.hs_s (hs_po hs).hsi_inv in
  if not (List.is_empty r) then
    failwith "hoare-wp: the statement is not wp-able";
  if not (EcReduction.is_conv hyps (hs_pr hs).inv pre) then
    failwith "hoare-wp: the precondition is not the weakest precondition";
  []

(* -------------------------------------------------------------------- *)
(* Rule (TCB). Its failures are reported as tactic errors. *)
let t_hoare_wp (r : hoare_wp) (tc : tcenv1) =
  let hyps = FApi.tc1_hyps tc in
  let hs   = tc1_as_hoareS tc in
  let subgoals =
    try  hoare_wp_subgoals hyps hs r
    with Failure msg -> tc_error !!tc ~who:"wp" "%s" msg in
  FApi.xrule1 tc (RHoareWp r) subgoals

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | RHoareWp n ->
         Some (EcPlRecheck.checker_of "hoare-wp" pf_as_hoareS
                 (fun hyps hs -> hoare_wp_subgoals hyps hs n))
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node): the surface [wp]. Compute the wp of the suffix
   after [i] (of the longest wp-able suffix when [i] is not given), split
   there with [seq], using that wp as intermediate assertion, and close the
   suffix premise with the rule. *)
let t_hoare_wp_full ?(uselet = true) (i : EcMatching.Position.codegap1 option) tc =
  let hyps = FApi.tc1_hyps tc in
  let hs   = tc1_as_hoareS tc in
  let s_hd, s_wp = o_split (LDecl.toenv hyps) i hs.hs_s in
  let r, pre =
    EcPlWp.wp ~uselet ~onesided:true
      hyps hs.hs_m (EcModules.stmt s_wp) (hs_po hs).hsi_inv in
  EcPlWp.check_wp_progress tc i r;
  let at  = List.length s_hd + List.length r in
  let at  = EcMatching.Position.(GapBefore (cpos1 at)) in
  let mid = { m = fst hs.hs_m; inv = pre; } in
  FApi.t_seqsub
    (EcHoareSeq.t_hoare_seq { hsr_at = at; hsr_mid = mid })
    [t_id; t_hoare_wp { hwp_uselet = uselet }]
    tc

(* -------------------------------------------------------------------- *)
(* Elaboration: the goal is known to be a [hoareS]. No position or a single
   one; positions are typed in the ambient environment. *)
let process_hoare_wp (cpos : EcParsetree.pdocodegap1) tc =
  let cpos = omap (EcTyping.trans_dcodegap1 (FApi.tc1_env tc)) cpos in
  match cpos with
  | None            -> t_hoare_wp_full None tc
  | Some (Single i) -> t_hoare_wp_full (Some i) tc
  | Some (Double _) -> tc_error_noXhl ~kinds:[`Equiv `Stmt] !!tc
