(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcAst

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* Parameters of the hoare [rndsem] tactic as supplied by the caller: high
   level, the position is still a symbolic code gap that must be resolved. *)
type hoare_rndsem_rule = {
  hrsr_at     : EcMatching.Position.codegap1;   (* start of the suffix *)
  hrsr_reduce : bool;                            (* sample only the variables of Q *)
}

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node): resolve the code gap to an index, reject
   exceptional postconditions (as before the migration), and apply the
   [rndsem] transformation through the hoare transformation rule. *)
let t_hoare_rndsem (r : hoare_rndsem_rule) (tc : tcenv1) =
  let env = FApi.tc1_env tc in
  let hs  = tc1_as_hoareS tc in
  let at  = s_split_index env r.hrsr_at hs.hs_s in
  if not (POE.is_empty (hs_po hs).hsi_inv) then
    tc_error !!tc "exceptions are not supported";
  let tr = EcTrRndSem.TrRndSem { trrs_at = at; trrs_reduce = r.hrsr_reduce } in
  EcHoareTransform.t_hoare_transform { htr_tr = tr } tc

(* -------------------------------------------------------------------- *)
(* Elaboration: the goal is known to be a [hoareS]. The position is typed
   first (with the side, which then makes a sided call fail there), then the
   tactic is applied. *)
let process_hoare_rndsem ~reduce (side : oside) pos (tc : tcenv1) =
  let pos = tc1_process_codegap1 tc (side, pos) in
  if is_some side then
    tc_error !!tc "invalid arguments";
  t_hoare_rndsem { hrsr_at = pos; hrsr_reduce = reduce } tc
