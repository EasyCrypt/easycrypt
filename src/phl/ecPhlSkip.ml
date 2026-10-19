(* -------------------------------------------------------------------- *)
open EcAst

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* The [skip] rules live, one module per logic, in [rules/<logic>/]. This
   module only keeps the logic-agnostic dispatcher. *)
let t_skip (tc : tcenv1) =
  match (FApi.tc1_goal tc).f_node with
  | FhoareS   _ -> EcHoareSkip.t_hoare_skip tc
  | FeHoareS  _ -> EcEHoareSkip.t_ehoare_skip tc
  | FbdHoareS _ -> EcBdHoareSkip.t_bdhoare_skip_full tc
  | FequivS   _ -> EcEquivSkip.t_equiv_skip tc
  | _ ->
      tc_error_noXhl
        ~kinds:[`Hoare `Stmt; `EHoare `Stmt; `PHoare `Stmt; `Equiv `Stmt]
        !!tc
