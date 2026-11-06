(* -------------------------------------------------------------------- *)
open EcAst

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* The existential rules live, one module per logic, in [rules/<logic>/]
   ([EcHoareExists], [EcEHoareExists], [EcBdHoareExists],
   [EcEquivExists]), their shared computations in [EcPlExists]; [ecall]
   is derived, in [EcHoareECall], [EcBdHoareECall] and [EcEquivECall],
   with its shared elaboration in [EcPlECall]. This module only keeps the
   legacy entry points (adapters onto those modules, so external callers
   and this module's interface are unchanged) and the logic-agnostic
   dispatchers. *)

(* -------------------------------------------------------------------- *)
let t_hr_exists_elim_r ?(bound : int option) (tc : tcenv1) =
  match (FApi.tc1_goal tc).f_node with
  | FhoareF _ | FhoareS _ ->
      EcHoareExists.t_hoare_exists_elim { hxe_bound = bound } tc
  | FeHoareF _ | FeHoareS _ ->
      EcEHoareExists.t_ehoare_exists_elim { ehxe_bound = bound } tc
  | FbdHoareF _ | FbdHoareS _ ->
      EcBdHoareExists.t_bdhoare_exists_elim { bxe_bound = bound } tc
  | FequivF _ | FequivS _ ->
      EcEquivExists.t_equiv_exists_elim { exe_bound = bound } tc
  | _ -> tc_error_noXhl ~kinds:hlkinds_Xhl !!tc

let t_hr_exists_elim (tc : tcenv1) =
  t_hr_exists_elim_r tc

(* -------------------------------------------------------------------- *)
let t_hr_exists_intro (fs : inv list) (tc : tcenv1) =
  let as_ss = function
    | Inv_ss f -> f
    | _ -> failwith "expected all invariants to have same kind" in
  let as_ts = function
    | Inv_ts f -> f
    | _ -> failwith "expected all invariants to have same kind" in

  match (FApi.tc1_goal tc).f_node with
  | FhoareF _ | FhoareS _ ->
      EcHoareExists.t_hoare_exists_intro (List.map as_ss fs) tc
  | FeHoareF _ | FeHoareS _ ->
      EcEHoareExists.t_ehoare_exists_intro (List.map as_ss fs) tc
  | FbdHoareF _ | FbdHoareS _ ->
      EcBdHoareExists.t_bdhoare_exists_intro (List.map as_ss fs) tc
  | FequivF _ | FequivS _ ->
      EcEquivExists.t_equiv_exists_intro (List.map as_ts fs) tc
  | _ -> tc_error_noXhl ~kinds:hlkinds_Xhl !!tc

(* -------------------------------------------------------------------- *)
let process_exists_intro ~(elim : bool) fs (tc : tcenv1) =
  match (FApi.tc1_goal tc).f_node with
  | FhoareF _ | FhoareS _ ->
      EcHoareExists.process_hoare_exists_intro ~elim fs tc
  | FeHoareF _ | FeHoareS _ ->
      EcEHoareExists.process_ehoare_exists_intro ~elim fs tc
  | FbdHoareF _ | FbdHoareS _ ->
      EcBdHoareExists.process_bdhoare_exists_intro ~elim fs tc
  | FequivF _ | FequivS _ ->
      EcEquivExists.process_equiv_exists_intro ~elim fs tc
  | _ -> tc_error_noXhl ~kinds:hlkinds_Xhl !!tc

(* -------------------------------------------------------------------- *)
let process_ecall dir oside pterm (tc : tcenv1) =
  match (FApi.tc1_goal tc).f_node with
  | FhoareS   _ -> EcHoareECall.process_hoare_ecall dir oside pterm tc
  | FbdHoareS _ -> EcBdHoareECall.process_bdhoare_ecall dir oside pterm tc
  | FequivS   _ -> EcEquivECall.process_equiv_ecall dir oside pterm tc
  | _ -> tc_error_noXhl ~kinds:[`Hoare `Stmt; `PHoare `Stmt; `Equiv `Stmt] !!tc
