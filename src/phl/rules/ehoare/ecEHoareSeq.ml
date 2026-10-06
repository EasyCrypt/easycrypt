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
(* Parameters of the ehoare [seq] rule as supplied by the caller: high level,
   the split position is still a symbolic code gap that must be resolved. *)
type ehoare_seq_rule = {
  ehsr_at  : EcMatching.Position.codegap1;   (* split position *)
  ehsr_mid : ss_inv;                          (* intermediate assertion *)
}

(* Low-level parameters recorded in the proof-node: the split position is the
   RESOLVED integer index. The checker recomputes the subgoals from this, so it
   never redoes code resolution. *)
type ehoare_seq_node = {
  ehsn_at  : EcMatching.Position.nm_codegap1;   (* resolved split index *)
  ehsn_mid : ss_inv;                             (* intermediate assertion *)
}

type EcCoreGoal.rule += REHoareSeq of ehoare_seq_node

(* -------------------------------------------------------------------- *)
(* Pure low-level core shared by the rule and its checker: split the statement
   at the already-resolved index and build the pre/mid and mid/post subgoals.
   Needs no environment — code resolution happened upstream, in the rule. *)
let ehoare_seq_subgoals (hs : eHoareS) (n : ehoare_seq_node) : form list =
  let phi    = ss_inv_rebind n.ehsn_mid (fst hs.ehs_m) in
  let s1, s2 = EcMatching.Position.split_at_nmcgap1 n.ehsn_at hs.ehs_s in
  let a = f_eHoareS (snd hs.ehs_m) (ehs_pr hs) (stmt s1) phi in
  let b = f_eHoareS (snd hs.ehs_m) phi (stmt s2) (ehs_po hs) in
  [a; b]

(* -------------------------------------------------------------------- *)
(* Rule (TCB): resolve the code gap to an index (the env-dependent step), record
   the resolved node, and build its subgoals through the shared core. The
   canonical rule takes the high-level record; the legacy positional interface
   (EcPhlSeq.t_ehoare_seq) adapts onto it. *)
let t_ehoare_seq (r : ehoare_seq_rule) tc =
  let env = FApi.tc1_env tc in
  let hs  = tc1_as_ehoareS tc in
  let n   = { ehsn_at  = s_split_index env r.ehsr_at hs.ehs_s;
              ehsn_mid = r.ehsr_mid; } in
  FApi.xrule1 tc (REHoareSeq n) (ehoare_seq_subgoals hs n)

(* -------------------------------------------------------------------- *)
(* Checker: rerun ONLY the low-level core on the recorded index (see
   [EcPhlRecheck]). *)
let () =
  register_rule_checker
    (function
     | REHoareSeq n ->
         Some (EcPhlRecheck.checker_of "ehoare-seq" pf_as_ehoareS
                 (fun _hyps hs -> ehoare_seq_subgoals hs n))
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* Elaboration: the goal is known to be an [eHoareS]. Validate the seq surface
   syntax for that logic (no side, no bound, single position and assertion),
   type the assertion and the split position, then apply the rule. *)
let process_ehoare_seq (info : seq_info) tc =
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
  let _, phi = TTC.tc1_process_Xhl_formula_xreal tc phi in
  let i = EcLowPhlGoal.tc1_process_codegap1 tc (info.seqi_side, i) in
  t_ehoare_seq { ehsr_at = i; ehsr_mid = phi } tc
