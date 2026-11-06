(* -------------------------------------------------------------------- *)
open EcFol
open EcAst

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* The rules closing trivially valid judgements live, one module per rule
   and logic, in [rules/<logic>/]: [true] (hoare), [zero] (ehoare) and
   [exfalso] (hoare, bdhoare, equiv). This module only keeps the legacy
   entry points and the logic-agnostic [exfalso] dispatcher. *)

(* -------------------------------------------------------------------- *)
let t_hoare_true = EcHoareTrue.t_hoare_true

let t_ehoare_zero = EcEHoareZero.t_ehoare_zero

(* -------------------------------------------------------------------- *)
(* An ehoare precondition is an expectation, never [false]: [exfalso] has no
   ehoare rule, and such goals are rejected by the precondition check. *)
let t_core_exfalso (tc : tcenv1) =
  let pre = tc1_get_pre tc in
  if not (f_equal (inv_of_inv pre) f_false) then
    tc_error !!tc "pre-condition is not `false'";
  match (FApi.tc1_goal tc).f_node with
  | FhoareS   _ -> EcHoareExfalso.t_hoareS_exfalso tc
  | FhoareF   _ -> EcHoareExfalso.t_hoareF_exfalso tc
  | FbdHoareS _ -> EcBdHoareExfalso.t_bdhoareS_exfalso tc
  | FbdHoareF _ -> EcBdHoareExfalso.t_bdhoareF_exfalso tc
  | FequivS   _ -> EcEquivExfalso.t_equivS_exfalso tc
  | FequivF   _ -> EcEquivExfalso.t_equivF_exfalso tc
  | _           -> tc_error !!tc "pre-condition is not `false'"
