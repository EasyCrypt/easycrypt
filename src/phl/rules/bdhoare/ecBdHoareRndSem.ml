(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* Parameters of the bdhoare [rndsem] tactic as supplied by the caller:
   high level, the position is still a symbolic code gap that must be
   resolved. *)
type bdhoare_rndsem_rule = {
  brsr_at     : EcMatching.Position.codegap1;   (* start of the suffix *)
  brsr_reduce : bool;                            (* sample only the variables of Q *)
}

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node): resolve the code gap to an index and apply the
   [rndsem] transformation through the bdhoare transformation rule. *)
let t_bdhoare_rndsem (r : bdhoare_rndsem_rule) (tc : tcenv1) =
  let env = FApi.tc1_env tc in
  let bhs = tc1_as_bdhoareS tc in
  let at  = s_split_index env r.brsr_at bhs.bhs_s in
  let tr  = EcTrRndSem.TrRndSem { trrs_at = at; trrs_reduce = r.brsr_reduce } in
  EcBdHoareTransform.t_bdhoare_transform { btr_tr = tr } tc

(* -------------------------------------------------------------------- *)
(* Elaboration: the goal is known to be a [bdHoareS]. The position is typed
   first (with the side, which then makes a sided call fail there), then the
   tactic is applied. *)
let process_bdhoare_rndsem ~reduce (side : oside) pos (tc : tcenv1) =
  let pos = tc1_process_codegap1 tc (side, pos) in
  if is_some side then
    tc_error !!tc "invalid arguments";
  t_bdhoare_rndsem { brsr_at = pos; brsr_reduce = reduce } tc
