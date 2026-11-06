(* -------------------------------------------------------------------- *)
open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* Parameters of the hoare [rcond] tactic as supplied by the caller: high
   level, the position is still symbolic and must be resolved. *)
type hoare_rcond_rule = {
  hrcr_at     : EcMatching.Position.codepos1;   (* position of the conditional *)
  hrcr_branch : bool;                            (* branch taken *)
}

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node): resolve the position (failing as before the
   migration when it is invalid or not a conditional) and apply the
   [rcond] transformation through the hoare transformation rule. *)
let t_hoare_rcond (r : hoare_rcond_rule) (tc : tcenv1) =
  let hs = tc1_as_hoareS tc in
  let at = EcPlRCond.resolve_rcond !!tc (FApi.tc1_env tc) r.hrcr_at hs.hs_s in
  let tr = EcTrRCond.TrRCond { trrc_at = at; trrc_branch = r.hrcr_branch } in
  EcHoareTransform.t_hoare_transform { htr_tr = tr } tc

(* -------------------------------------------------------------------- *)
(* Elaboration: the goal is known to be a [hoareS]. Type the position in
   its memory, then apply the tactic. *)
let process_hoare_rcond (b : bool) (at : EcParsetree.pcodepos1) (tc : tcenv1) =
  let at = tc1_process_codepos1 tc (None, at) in
  t_hoare_rcond { hrcr_at = at; hrcr_branch = b } tc
