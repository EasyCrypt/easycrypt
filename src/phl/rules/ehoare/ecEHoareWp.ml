(* -------------------------------------------------------------------- *)
open EcUtils
open EcAst
open EcEnv

open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* Parameter of the ehoare [wp] rule: whether the weakest pre-expectation
   let-binds its substitutions. Nothing to resolve: the same record is the
   rule argument and the node payload. *)
type ehoare_wp = {
  ehwp_uselet : bool;
}

type EcCoreGoal.rule += REHoareWp of ehoare_wp

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. The rule has no premise;
   its side conditions (the statement is entirely wp-able, the
   pre-expectation is its weakest pre-expectation) are part of it, so the
   checker re-validates them. *)
let ehoare_wp_subgoals (hyps : LDecl.hyps) (hs : eHoareS) (n : ehoare_wp) =
  let r, pre =
    EcPlWp.ewp ~uselet:n.ehwp_uselet
      (LDecl.toenv hyps) hs.ehs_m hs.ehs_s (ehs_po hs).inv in
  if not (List.is_empty r) then
    failwith "ehoare-wp: the statement is not wp-able";
  if not (EcReduction.is_conv hyps (ehs_pr hs).inv pre) then
    failwith "ehoare-wp: the pre-expectation is not the weakest one";
  []

(* -------------------------------------------------------------------- *)
(* Rule (TCB). Its failures are reported as tactic errors. *)
let t_ehoare_wp (r : ehoare_wp) (tc : tcenv1) =
  let hyps = FApi.tc1_hyps tc in
  let hs   = tc1_as_ehoareS tc in
  let subgoals =
    try  ehoare_wp_subgoals hyps hs r
    with Failure msg -> tc_error !!tc ~who:"wp" "%s" msg in
  FApi.xrule1 tc (REHoareWp r) subgoals

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | REHoareWp n ->
         Some (EcPlRecheck.checker_of "ehoare-wp" pf_as_ehoareS
                 (fun hyps hs -> ehoare_wp_subgoals hyps hs n))
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node): the surface [wp]. Compute the weakest
   pre-expectation of the suffix after [i] (of the longest wp-able suffix
   when [i] is not given), split there with [seq], using it as
   intermediate expectation, and close the suffix premise with the rule. *)
let t_ehoare_wp_full ?(uselet = true) (i : EcMatching.Position.codegap1 option) tc =
  let env = FApi.tc1_env tc in
  let hs  = tc1_as_ehoareS tc in
  let s_hd, s_wp = o_split env i hs.ehs_s in
  let r, pre =
    EcPlWp.ewp ~uselet env hs.ehs_m (EcModules.stmt s_wp) (ehs_po hs).inv in
  EcPlWp.check_wp_progress tc i r;
  let at  = List.length s_hd + List.length r in
  let at  = EcMatching.Position.(GapBefore (cpos1 at)) in
  let mid = { m = fst hs.ehs_m; inv = pre; } in
  FApi.t_seqsub
    (EcEHoareSeq.t_ehoare_seq { ehsr_at = at; ehsr_mid = mid })
    [t_id; t_ehoare_wp { ehwp_uselet = uselet }]
    tc

(* -------------------------------------------------------------------- *)
(* Elaboration: the goal is known to be an [eHoareS]. No position or a
   single one; positions are typed in the ambient environment. *)
let process_ehoare_wp (cpos : EcParsetree.pdocodegap1) tc =
  let cpos = omap (EcTyping.trans_dcodegap1 (FApi.tc1_env tc)) cpos in
  match cpos with
  | None            -> t_ehoare_wp_full None tc
  | Some (Single i) -> t_ehoare_wp_full (Some i) tc
  | Some (Double _) -> tc_error_noXhl ~kinds:[`Equiv `Stmt] !!tc
