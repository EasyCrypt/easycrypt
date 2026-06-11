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
(* Parameters of the hoare [seq] rule. Recorded in the proof-node, so the
   checker can recompute the rule's subgoals. *)
type hoare_seq_rule = {
  hsr_at  : EcMatching.Position.codegap1;   (* split position *)
  hsr_mid : ss_inv;                          (* intermediate assertion *)
}

type EcCoreGoal.rule += RHoareSeq of hoare_seq_rule

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule (to build the subgoals) and its checker (to
   recompute and re-validate them): splitting a [hoareS] statement at [hsr_at]
   with intermediate assertion [hsr_mid] yields the pre/mid and mid/post goals.
   It takes the goal's hypotheses (its environment is [LDecl.toenv] of them) so
   the rule and checker share the same context. *)
let hoare_seq_subgoals hyps (hs : sHoareS) (r : hoare_seq_rule) : form list =
  let env    = EcEnv.LDecl.toenv hyps in
  let phi    = ss_inv_rebind r.hsr_mid (fst hs.hs_m) in
  let s1, s2 = s_split env r.hsr_at hs.hs_s in
  let post   = update_hs_ss phi (hs_po hs) in
  let a = f_hoareS (snd hs.hs_m) (hs_pr hs) (stmt s1) post in
  let b = f_hoareS (snd hs.hs_m) phi (stmt s2) (hs_po hs) in
  [a; b]

(* -------------------------------------------------------------------- *)
(* Rule (TCB): split according to [r], emit a recheckable node recording it.
   This canonical rule takes the parameter record; the legacy positional
   interface (EcPhlSeq.t_hoare_seq) adapts onto it. *)
let t_hoare_seq_r (r : hoare_seq_rule) tc =
  let hs = tc1_as_hoareS tc in
  FApi.xrule1 tc (RHoareSeq r) (hoare_seq_subgoals (FApi.tc1_hyps tc) hs r)

let t_hoare_seq = FApi.t_low1 "hoare-seq" t_hoare_seq_r

(* -------------------------------------------------------------------- *)
(* Checker: read the judgement, rerun the shared builder on the recorded params,
   and compare against the stored subgoals (see [EcPhlRecheck]). *)
let () =
  register_rule_checker
    (function
     | RHoareSeq r ->
         Some (EcPhlRecheck.checker_of "hoare-seq" pf_as_hoareS
                 (fun hyps hs -> hoare_seq_subgoals hyps hs r))
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* Elaboration: the goal is known to be a [hoareS]. Validate the seq surface
   syntax for that logic (no side, no bound, single position and assertion),
   type the assertion and the split position, then apply the rule. *)
let process_hoare_seq (info : seq_info) tc =
  if is_some info.seqi_side then
    tc_error !!tc "seq: no side information expected";
  begin match info.seqi_bd with
  | PSeqNone -> ()
  | _        -> tc_error !!tc "seq: no bound information expected" end;
  let i =
    match info.seqi_at with
    | Single i -> i
    | Double _ -> tc_error !!tc "seq: a single position is expected" in
  let phi =
    match info.seqi_mid with
    | Single phi -> phi
    | Double _   -> tc_error !!tc "seq: a single formula is expected" in
  let _, phi = TTC.tc1_process_Xhl_formula tc phi in
  let i = EcLowPhlGoal.tc1_process_codegap1 tc (info.seqi_side, i) in
  t_hoare_seq { hsr_at = i; hsr_mid = phi } tc
