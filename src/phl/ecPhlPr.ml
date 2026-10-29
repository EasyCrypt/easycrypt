(* -------------------------------------------------------------------- *)
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* The [pr] rules (bdhoare, equiv) and the [prbounded] rules live in
   [rules/<logic>/]; the hoare [pr] tactic is derived. This module only
   keeps the dispatcher and the legacy entry points. *)
let t_hoare_ppr   = EcHoarePr.t_hoareF_pr
let t_bdhoare_ppr = EcBdHoarePr.t_bdhoareF_pr

let t_equiv_ppr ty phi_l phi_r =
  EcEquivPr.(t_equivF_pr { epr_ty = ty; epr_left = phi_l; epr_right = phi_r; })

(* -------------------------------------------------------------------- *)
let process_ppr info tc =
  match info with
  | None ->
      t_hF_or_bhF_or_eF ~th:t_hoare_ppr ~tbh:t_bdhoare_ppr tc

  | Some phis ->
      EcEquivPr.process_equivF_pr phis tc

(* -------------------------------------------------------------------- *)
let t_prbounded conseq = EcBdHoarePrBounded.t_bdhoare_prbounded ~conseq
