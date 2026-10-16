(* -------------------------------------------------------------------- *)
open EcParsetree

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* Parameters of the (one-sided) equiv [rcond] tactic as supplied by the
   caller: high level, the position is still symbolic and must be
   resolved. *)
type equiv_rcond_rule = {
  ercr_side   : side;                            (* side of the conditional *)
  ercr_at     : EcMatching.Position.codepos1;   (* position of the conditional *)
  ercr_branch : bool;                            (* branch taken *)
}

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node): resolve the position on the chosen side
   (failing as before the migration when it is invalid or not a
   conditional) and apply the [rcond] transformation to that side through
   the equiv transformation rule. *)
let t_equiv_rcond (r : equiv_rcond_rule) (tc : tcenv1) =
  let es = tc1_as_equivS tc in
  let s  = sideif r.ercr_side es.es_sl es.es_sr in
  let at = EcPlRCond.resolve_rcond !!tc (FApi.tc1_env tc) r.ercr_at s in
  let tr = EcTrRCond.TrRCond { trrc_at = at; trrc_branch = r.ercr_branch } in
  EcEquivTransform.t_equiv_transform { etr_side = r.ercr_side; etr_tr = tr } tc

(* -------------------------------------------------------------------- *)
(* Elaboration: the goal is known to be an [equivS] (or is reported as not
   being one when typing the position). Type the position in the memory of
   [side], then apply the tactic. *)
let process_equiv_rcond (side : side) (b : bool) (at : pcodepos1) (tc : tcenv1) =
  let at = tc1_process_codepos1 tc (Some side, at) in
  t_equiv_rcond { ercr_side = side; ercr_at = at; ercr_branch = b } tc
