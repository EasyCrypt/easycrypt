(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcFol
open EcAst
open EcSubst

open EcCoreGoal
open EcLowPhlGoal

module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
(* Recheckable proof-node for the hoare [seq] rule. It records the split
   position and the intermediate assertion, which is exactly what the checker
   needs to recompute the rule's subgoals. *)
type EcCoreGoal.rule += RHoareSeq of EcMatching.Position.codegap1 * ss_inv

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule (to build the subgoals) and its checker (to
   recompute and re-validate them): splitting a [hoareS] statement at [i] with
   intermediate assertion [phi] yields the pre/[phi] and [phi]/post goals. *)
let hoare_seq_subgoals env (hs : sHoareS) i (phi : ss_inv) : form list =
  let phi    = ss_inv_rebind phi (fst hs.hs_m) in
  let s1, s2 = s_split env i hs.hs_s in
  let post   = update_hs_ss phi (hs_po hs) in
  let a = f_hoareS (snd hs.hs_m) (hs_pr hs) (stmt s1) post in
  let b = f_hoareS (snd hs.hs_m) phi (stmt s2) (hs_po hs) in
  [a; b]

(* -------------------------------------------------------------------- *)
(* Rule (TCB): split at [i], emit a recheckable node recording its params. *)
let t_hoare_seq_r i phi tc =
  let env = FApi.tc1_env tc in
  let hs  = tc1_as_hoareS tc in
  FApi.xrule1 tc (RHoareSeq (i, phi)) (hoare_seq_subgoals env hs i phi)

let t_hoare_seq = FApi.t_low2 "hoare-seq" t_hoare_seq_r

(* -------------------------------------------------------------------- *)
(* Checker: recompute the subgoals from the recorded params and confirm they
   match (up to conversion) what the node stored. *)
let check_hoare_seq i phi (pe : proofenv) (goal : pregoal) (subs : pregoal list) =
  let hyps     = goal.g_hyps in
  let env      = EcEnv.LDecl.toenv hyps in
  let hs       = pf_as_hoareS pe goal.g_concl in
  let expected = hoare_seq_subgoals env hs i phi in
  let actual   = List.map (fun (g : pregoal) -> g.g_concl) subs in
  if List.length expected <> List.length actual then
    raise (RecheckFailure "hoare-seq: wrong number of subgoals");
  List.iter2
    (fun e a ->
      if not (EcReduction.is_conv hyps e a) then
        raise (RecheckFailure "hoare-seq: subgoal mismatch"))
    expected actual

let () =
  register_rule_checker
    (function
     | RHoareSeq (i, phi) -> Some (check_hoare_seq i phi)
     | _                  -> None)

(* -------------------------------------------------------------------- *)
(* Elaboration: the goal is known to be a [hoareS]. Type the intermediate
   assertion and the split position, then apply the rule. *)
let process_hoare_seq (side : oside) i (phi : pformula) tc =
  if is_some side then
    tc_error !!tc "seq: no side information expected";
  let _, phi = TTC.tc1_process_Xhl_formula tc phi in
  let i = EcLowPhlGoal.tc1_process_codegap1 tc (side, i) in
  t_hoare_seq i phi tc
