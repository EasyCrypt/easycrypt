(* -------------------------------------------------------------------- *)
open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* Parameters of the bdhoare [rcond] tactic as supplied by the caller: high
   level, the position is still symbolic and must be resolved. *)
type bdhoare_rcond_rule = {
  brcr_at     : EcMatching.Position.codepos1;   (* position of the conditional *)
  brcr_branch : bool;                            (* branch taken *)
}

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node): resolve the position (failing as before the
   migration when it is invalid or not a conditional) and apply the
   [rcond] transformation through the bdhoare transformation rule. *)
let t_bdhoare_rcond (r : bdhoare_rcond_rule) (tc : tcenv1) =
  let bhs = tc1_as_bdhoareS tc in
  let at  = EcPlRCond.resolve_rcond !!tc (FApi.tc1_env tc) r.brcr_at bhs.bhs_s in
  let tr  = EcTrRCond.TrRCond { trrc_at = at; trrc_branch = r.brcr_branch } in
  EcBdHoareTransform.t_bdhoare_transform { btr_tr = tr } tc

(* -------------------------------------------------------------------- *)
(* Elaboration: the goal is known to be a [bdHoareS]. Type the position in
   its memory, then apply the tactic. *)
let process_bdhoare_rcond (b : bool) (at : EcParsetree.pcodepos1) (tc : tcenv1) =
  let at = tc1_process_codepos1 tc (None, at) in
  t_bdhoare_rcond { brcr_at = at; brcr_branch = b } tc
