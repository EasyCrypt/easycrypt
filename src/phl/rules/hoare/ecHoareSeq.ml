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
(* Parameters of the hoare [seq] rule as supplied by the caller: high level, the
   split position is still a symbolic code gap that must be resolved. *)
type hoare_seq_rule = {
  hsr_at  : EcMatching.Position.codegap1;   (* split position *)
  hsr_mid : ss_inv;                          (* intermediate assertion *)
}

(* Low-level parameters recorded in the proof-node: the split position is the
   RESOLVED integer index. The checker recomputes the subgoals from this, so it
   never redoes code resolution. *)
type hoare_seq_node = {
  hsn_at  : EcMatching.Position.nm_codegap1;   (* resolved split index *)
  hsn_mid : ss_inv;                             (* intermediate assertion *)
}

type EcCoreGoal.rule += RHoareSeq of hoare_seq_node

(* -------------------------------------------------------------------- *)
(* Pure low-level core shared by the rule and its checker: split the statement
   at the already-resolved index and build the pre/mid and mid/post subgoals.
   Needs no environment — code resolution happened upstream, in the rule. *)
let hoare_seq_subgoals (hs : sHoareS) (n : hoare_seq_node) : form list =
  let phi    = ss_inv_rebind n.hsn_mid (fst hs.hs_m) in
  let s1, s2 = EcMatching.Position.split_at_nmcgap1 n.hsn_at hs.hs_s in
  let post   = update_hs_ss phi (hs_po hs) in
  let a = f_hoareS (snd hs.hs_m) (hs_pr hs) (stmt s1) post in
  let b = f_hoareS (snd hs.hs_m) phi (stmt s2) (hs_po hs) in
  [a; b]

(* -------------------------------------------------------------------- *)
(* Rule (TCB): resolve the code gap to an index (the env-dependent step), record
   the resolved node, and build its subgoals through the shared core. The
   canonical rule takes the high-level record; the legacy positional interface
   (EcPhlSeq.t_hoare_seq) adapts onto it. *)
let t_hoare_seq_r (r : hoare_seq_rule) tc =
  let env = FApi.tc1_env tc in
  let hs  = tc1_as_hoareS tc in
  let n   = { hsn_at  = s_split_index env r.hsr_at hs.hs_s;
              hsn_mid = r.hsr_mid; } in
  FApi.xrule1 tc (RHoareSeq n) (hoare_seq_subgoals hs n)

let t_hoare_seq = FApi.t_low1 "hoare-seq" t_hoare_seq_r

(* -------------------------------------------------------------------- *)
(* Checker: rerun ONLY the low-level core on the recorded index (see
   [EcPhlRecheck]). It never redoes code resolution, so [normalize_cgap1] stays
   out of its trust boundary. *)
let () =
  register_rule_checker
    (function
     | RHoareSeq n ->
         Some (EcPhlRecheck.checker_of "hoare-seq" pf_as_hoareS
                 (fun _hyps hs -> hoare_seq_subgoals hs n))
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
