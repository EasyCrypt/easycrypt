(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcFol
open EcAst
open EcEnv

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* Parameters of the bdhoare [rndsem] rule as supplied by the caller: high
   level, the position is still a symbolic code gap that must be resolved. *)
type bdhoare_rndsem_rule = {
  brsr_at     : EcMatching.Position.codegap1;   (* start of the suffix *)
  brsr_reduce : bool;                            (* sample only the variables of Q *)
}

(* Low-level parameters recorded in the proof-node: the position is the
   RESOLVED integer index. *)
type bdhoare_rndsem_node = {
  brsn_at     : EcMatching.Position.nm_codegap1;   (* resolved index *)
  brsn_reduce : bool;
}

type EcCoreGoal.rule += RBdHoareRndSem of bdhoare_rndsem_node

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker: replace the suffix by its
   semantic sampling. Its side condition (a straight-line suffix writing no
   global) is part of it, so the checker re-validates it. *)
let bdhoare_rndsem_subgoals
    (hyps : LDecl.hyps) (bhs : bdHoareS) (n : bdhoare_rndsem_node)
=
  let env = LDecl.toenv hyps in
  let s1, s2 = EcMatching.Position.split_at_nmcgap1 n.brsn_at bhs.bhs_s in
  let fv =
    if   n.brsn_reduce
    then Some (EcPV.PV.fv env (fst bhs.bhs_m) (bhs_po bhs).inv)
    else None in
  let (_, mt), s2 = EcPlRndSem.semrnd env bhs.bhs_m fv s2 in
  [f_bdHoareS mt (bhs_pr bhs) (stmt (s1 @ s2)) (bhs_po bhs) bhs.bhs_cmp (bhs_bd bhs)]

(* -------------------------------------------------------------------- *)
(* Rule (TCB): resolve the code gap to an index, record the resolved node,
   and build its subgoal through the shared core. *)
let t_bdhoare_rndsem (r : bdhoare_rndsem_rule) (tc : tcenv1) =
  let env = FApi.tc1_env tc in
  let bhs = tc1_as_bdhoareS tc in
  let n   = { brsn_at     = s_split_index env r.brsr_at bhs.bhs_s;
              brsn_reduce = r.brsr_reduce; } in
  let sg =
    try  bdhoare_rndsem_subgoals (FApi.tc1_hyps tc) bhs n
    with EcPlRndSem.InvalidSemRnd -> tc_error !!tc "semrnd" in
  FApi.xrule1 tc (RBdHoareRndSem n) sg

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | RBdHoareRndSem n ->
         Some (EcPlRecheck.checker_of "bdhoare-rndsem" pf_as_bdhoareS
                 (fun hyps bhs -> bdhoare_rndsem_subgoals hyps bhs n))
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* Elaboration: the goal is known to be a [bdHoareS]. The position is typed
   first (with the side, which then makes a sided call fail there), then the
   rule is applied. *)
let process_bdhoare_rndsem ~reduce (side : oside) pos (tc : tcenv1) =
  let pos = tc1_process_codegap1 tc (side, pos) in
  if is_some side then
    tc_error !!tc "invalid arguments";
  t_bdhoare_rndsem { brsr_at = pos; brsr_reduce = reduce } tc
