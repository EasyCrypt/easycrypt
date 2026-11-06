(* -------------------------------------------------------------------- *)
open EcParsetree

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* Parameters of the equiv [rndsem] tactic as supplied by the caller: high
   level, the position is still a symbolic code gap that must be resolved. *)
type equiv_rndsem_rule = {
  ersr_side   : side;                            (* rewritten side *)
  ersr_at     : EcMatching.Position.codegap1;   (* start of the suffix *)
  ersr_reduce : bool;                            (* sample only the variables of Q *)
}

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node): resolve the code gap to an index on the chosen
   side and apply the [rndsem] transformation to that side through the
   equiv transformation rule. *)
let t_equiv_rndsem (r : equiv_rndsem_rule) (tc : tcenv1) =
  let env = FApi.tc1_env tc in
  let es  = tc1_as_equivS tc in
  let s   = sideif r.ersr_side es.es_sl es.es_sr in
  let at  = s_split_index env r.ersr_at s in
  let tr  = EcTrRndSem.TrRndSem { trrs_at = at; trrs_reduce = r.ersr_reduce } in
  EcEquivTransform.t_equiv_transform { etr_side = r.ersr_side; etr_tr = tr } tc

(* -------------------------------------------------------------------- *)
(* Elaboration: the goal is known to be an [equivS]. The position is typed
   first, in the memory of the side (which then makes an unsided call fail
   there), then the tactic is applied. *)
let process_equiv_rndsem ~reduce (side : oside) pos (tc : tcenv1) =
  let pos = tc1_process_codegap1 tc (side, pos) in
  match side with
  | None -> tc_error !!tc "invalid arguments"
  | Some side ->
      t_equiv_rndsem { ersr_side = side; ersr_at = pos; ersr_reduce = reduce } tc
