(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcFol
open EcAst
open EcEnv

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* Parameters of the hoare [rndsem] rule as supplied by the caller: high
   level, the position is still a symbolic code gap that must be resolved. *)
type hoare_rndsem_rule = {
  hrsr_at     : EcMatching.Position.codegap1;   (* start of the suffix *)
  hrsr_reduce : bool;                            (* sample only the variables of Q *)
}

(* Low-level parameters recorded in the proof-node: the position is the
   RESOLVED integer index. *)
type hoare_rndsem_node = {
  hrsn_at     : EcMatching.Position.nm_codegap1;   (* resolved index *)
  hrsn_reduce : bool;
}

type EcCoreGoal.rule += RHoareRndSem of hoare_rndsem_node

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker: replace the suffix by its
   semantic sampling. Its side conditions (no exceptional postcondition, a
   straight-line suffix writing no global) are part of it, so the checker
   re-validates them. *)
let hoare_rndsem_subgoals (hyps : LDecl.hyps) (hs : sHoareS) (n : hoare_rndsem_node) =
  let env = LDecl.toenv hyps in
  if not (POE.is_empty (hs_po hs).hsi_inv) then
    failwith "hoare-rndsem: exceptions are not supported";
  let s1, s2 = EcMatching.Position.split_at_nmcgap1 n.hrsn_at hs.hs_s in
  let post = POE.lower (hs_po hs) in
  let fv =
    if n.hrsn_reduce then Some (EcPV.PV.fv env (fst hs.hs_m) post.inv) else None in
  let (_, mt), s2 = EcPlRndSem.semrnd env hs.hs_m fv s2 in
  [f_hoareS mt (hs_pr hs) (stmt (s1 @ s2)) (hs_po hs)]

(* -------------------------------------------------------------------- *)
(* Rule (TCB): resolve the code gap to an index, record the resolved node,
   and build its subgoal through the shared core. *)
let t_hoare_rndsem (r : hoare_rndsem_rule) (tc : tcenv1) =
  let env = FApi.tc1_env tc in
  let hs  = tc1_as_hoareS tc in
  let n   = { hrsn_at     = s_split_index env r.hrsr_at hs.hs_s;
              hrsn_reduce = r.hrsr_reduce; } in
  if not (POE.is_empty (hs_po hs).hsi_inv) then
    tc_error !!tc "exceptions are not supported";
  let sg =
    try  hoare_rndsem_subgoals (FApi.tc1_hyps tc) hs n
    with EcPlRndSem.InvalidSemRnd -> tc_error !!tc "semrnd" in
  FApi.xrule1 tc (RHoareRndSem n) sg

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | RHoareRndSem n ->
         Some (EcPlRecheck.checker_of "hoare-rndsem" pf_as_hoareS
                 (fun hyps hs -> hoare_rndsem_subgoals hyps hs n))
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* Elaboration: the goal is known to be a [hoareS]. The position is typed
   first (with the side, which then makes a sided call fail there), then the
   rule is applied. *)
let process_hoare_rndsem ~reduce (side : oside) pos (tc : tcenv1) =
  let pos = tc1_process_codegap1 tc (side, pos) in
  if is_some side then
    tc_error !!tc "invalid arguments";
  t_hoare_rndsem { hrsr_at = pos; hrsr_reduce = reduce } tc
