(* -------------------------------------------------------------------- *)
open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* Parameters of the ehoare [rcond] tactic as supplied by the caller: high
   level, the position is still symbolic and must be resolved. *)
type ehoare_rcond_rule = {
  ehrcr_at     : EcMatching.Position.codepos1;   (* position of the conditional *)
  ehrcr_branch : bool;                            (* branch taken *)
}

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node): resolve the position (failing as before the
   migration when it is invalid or not a conditional) and apply the
   [rcond] transformation through the ehoare transformation rule (which
   checks the form of the precondition). *)
let t_ehoare_rcond (r : ehoare_rcond_rule) (tc : tcenv1) =
  let hs = tc1_as_ehoareS tc in
  let at = EcPlRCond.resolve_rcond !!tc (FApi.tc1_env tc) r.ehrcr_at hs.ehs_s in
  let tr = EcTrRCond.TrRCond { trrc_at = at; trrc_branch = r.ehrcr_branch } in
  EcEHoareTransform.t_ehoare_transform { ehtr_tr = tr } tc

(* -------------------------------------------------------------------- *)
(* Elaboration: the goal is known to be an [eHoareS] (or is reported as not
   being one when typing the position). Type the position in its memory,
   then apply the tactic. *)
let process_ehoare_rcond (b : bool) (at : EcParsetree.pcodepos1) (tc : tcenv1) =
  let at = tc1_process_codepos1 tc (None, at) in
  t_ehoare_rcond { ehrcr_at = at; ehrcr_branch = b } tc
