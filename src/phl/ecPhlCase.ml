(* --------------------------------------------------------------------- *)
open EcAst

open EcCoreGoal
open EcLowPhlGoal

(* --------------------------------------------------------------------- *)
(* The [case] rules live, one module per logic, in [rules/<logic>/]. This
   module only keeps the legacy positional entry points (adapters onto
   those rules, so that external callers and this module's interface are
   unchanged) and the logic-agnostic dispatcher. *)

(* --------------------------------------------------------------------- *)
let t_hoare_case ?(simplify = true) f =
  EcHoareCase.(t_hoare_case { hca_cond = f; hca_simplify = simplify })

let t_bdhoare_case ?(simplify = true) f =
  EcBdHoareCase.(t_bdhoare_case { bca_cond = f; bca_simplify = simplify })

let t_equiv_case ?(simplify = true) f =
  EcEquivCase.(t_equiv_case { eca_cond = f; eca_simplify = simplify })

(* --------------------------------------------------------------------- *)
(* Dispatch on the formula kind and the goal kind. The ehoare rule has no
   [simplify] option: its precondition is not a conjunction. *)
let t_hl_case ?simplify f tc =
  match f, (FApi.tc1_goal tc).f_node with
  | Inv_hs _, _ -> assert false

  | Inv_ss f, FhoareS   _ -> t_hoare_case   ?simplify f tc
  | Inv_ss f, FeHoareS  _ -> EcEHoareCase.(t_ehoare_case { ehca_cond = f }) tc
  | Inv_ss f, FbdHoareS _ -> t_bdhoare_case ?simplify f tc
  | Inv_ss _, FequivS   _ -> tc_error !!tc "expecting a two sided formula"

  | Inv_ts f, FequivS _ -> t_equiv_case ?simplify f tc
  | Inv_ts _, (FhoareS _ | FeHoareS _ | FbdHoareS _) ->
      tc_error !!tc "expecting a one sided formula"

  | _, _ ->
      tc_error_noXhl
        ~kinds:[`Hoare `Stmt; `EHoare `Stmt; `PHoare `Stmt; `Equiv `Stmt]
        !!tc
