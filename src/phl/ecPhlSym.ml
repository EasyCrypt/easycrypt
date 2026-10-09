(* -------------------------------------------------------------------- *)
open EcAst

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* The [sym] rules (statement and procedure equiv) live in
   [rules/equiv/ecEquivSym.ml]. This module only keeps the dispatcher. *)
let t_equiv_sym (tc : tcenv1) =
  match (FApi.tc1_goal tc).f_node with
  | FequivF _ -> EcEquivSym.t_equivF_sym tc
  | FequivS _ -> EcEquivSym.t_equivS_sym tc
  | _ -> tc_error_noXhl ~kinds:[`Equiv `Any] !!tc
