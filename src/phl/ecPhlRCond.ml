(* -------------------------------------------------------------------- *)
open EcAst

open EcCoreGoal

(* -------------------------------------------------------------------- *)
(* The [rcond] and [match C k] tactics are derived, one module per logic in
   [rules/<logic>/] (EcHoareRCond, EcHoareRMatch, ...): they apply the
   [rcond] / [rmatch] program transformations ([EcTrRCond], [EcTrRMatch])
   through the transformation rule of the logic, or the framed [rmatch]
   rule of the logic. This module only keeps the legacy positional entry
   points (adapters onto those tactics, so external callers and this
   module's interface are unchanged) and the logic-agnostic dispatchers. *)

(* -------------------------------------------------------------------- *)
module Low = struct
  let t_hoare_rcond b at_pos =
    EcHoareRCond.(t_hoare_rcond { hrcr_at = at_pos; hrcr_branch = b })

  let t_ehoare_rcond b at_pos =
    EcEHoareRCond.(t_ehoare_rcond { ehrcr_at = at_pos; ehrcr_branch = b })

  let t_bdhoare_rcond b at_pos =
    EcBdHoareRCond.(t_bdhoare_rcond { brcr_at = at_pos; brcr_branch = b })

  let t_equiv_rcond side b at_pos =
    EcEquivRCond.(t_equiv_rcond
      { ercr_side = side; ercr_at = at_pos; ercr_branch = b })
end

(* -------------------------------------------------------------------- *)
(* Dispatch on the goal kind only. Without a side, a goal that is neither a
   [bdHoareS] nor a [hoareS] goes to the ehoare tactic, which reports it. *)
let t_rcond side b at_pos tc =
  match side, (FApi.tc1_goal tc).f_node with
  | None, FbdHoareS _ -> Low.t_bdhoare_rcond b at_pos tc
  | None, FhoareS   _ -> Low.t_hoare_rcond b at_pos tc
  | None, _           -> Low.t_ehoare_rcond b at_pos tc
  | Some side, _      -> Low.t_equiv_rcond side b at_pos tc

let process_rcond side b at_pos tc =
  match side, (FApi.tc1_goal tc).f_node with
  | None, FbdHoareS _ -> EcBdHoareRCond.process_bdhoare_rcond b at_pos tc
  | None, FhoareS   _ -> EcHoareRCond.process_hoare_rcond b at_pos tc
  | None, _           -> EcEHoareRCond.process_ehoare_rcond b at_pos tc
  | Some side, _      -> EcEquivRCond.process_equiv_rcond side b at_pos tc

(* -------------------------------------------------------------------- *)
module LowMatch = struct
  let t_hoare_rcond_match c at_pos =
    EcHoareRMatch.(t_hoare_rmatch { hrmr_at = at_pos; hrmr_ctor = c })

  let t_bdhoare_rcond_match c at_pos =
    EcBdHoareRMatch.(t_bdhoare_rmatch { brmr_at = at_pos; brmr_ctor = c })

  let t_equiv_rcond_match side c at_pos =
    EcEquivRMatch.(t_equiv_rmatch
      { ermr_side = side; ermr_at = at_pos; ermr_ctor = c })
end

(* -------------------------------------------------------------------- *)
(* Dispatch on the goal kind only. Without a side, a goal that is neither a
   [bdHoareS] nor an [eHoareS] goes to the hoare tactic, which reports it. *)
let t_rcond_match side c at_pos tc =
  match side, (FApi.tc1_goal tc).f_node with
  | None, FbdHoareS _ -> LowMatch.t_bdhoare_rcond_match c at_pos tc
  | None, FeHoareS  _ ->
      EcEHoareRMatch.(t_ehoare_rmatch { ehrmr_at = at_pos; ehrmr_ctor = c }) tc
  | None, _           -> LowMatch.t_hoare_rcond_match c at_pos tc
  | Some side, _      -> LowMatch.t_equiv_rcond_match side c at_pos tc

let process_rcond_match side c at_pos tc =
  match side, (FApi.tc1_goal tc).f_node with
  | None, FbdHoareS _ -> EcBdHoareRMatch.process_bdhoare_rmatch c at_pos tc
  | None, FeHoareS  _ -> EcEHoareRMatch.process_ehoare_rmatch c at_pos tc
  | None, _           -> EcHoareRMatch.process_hoare_rmatch c at_pos tc
  | Some side, _      -> EcEquivRMatch.process_equiv_rmatch side c at_pos tc
