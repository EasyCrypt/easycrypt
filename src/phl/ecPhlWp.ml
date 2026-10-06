(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcAst

open EcCoreGoal
open EcLowPhlGoal
open EcMatching.Position

(* -------------------------------------------------------------------- *)
(* The [wp] rules live, one module per logic, in [rules/<logic>/], and the
   wp computation they share in [rules/ecPlWp.ml]. This module only keeps
   the logic-agnostic dispatchers. *)

(* -------------------------------------------------------------------- *)
(* The goal kinds accepted by [wp], depending on its position(s). *)
let wp_error (k : 'a doption option) (tc : tcenv1) =
  let kinds =
    match k with
    | None            -> [`Hoare `Stmt; `EHoare `Stmt; `PHoare `Stmt; `Equiv `Stmt]
    | Some (Single _) -> [`Hoare `Stmt; `EHoare `Stmt; `PHoare `Stmt]
    | Some (Double _) -> [`Equiv `Stmt] in
  tc_error_noXhl ~kinds !!tc

(* -------------------------------------------------------------------- *)
let t_wp ?(uselet = true) (k : codegap1 doption option) (tc : tcenv1) =
  let single = function Some (Single i) -> Some i | _ -> None in
  let double = function Some (Double ij) -> Some ij | _ -> None in
  match (FApi.tc1_goal tc).f_node, k with
  | FhoareS _, (None | Some (Single _)) ->
      EcHoareWp.t_hoare_wp_full ~uselet (single k) tc
  | FeHoareS _, (None | Some (Single _)) ->
      EcEHoareWp.t_ehoare_wp_full ~uselet (single k) tc
  | FbdHoareS _, (None | Some (Single _)) ->
      EcBdHoareWp.(t_bdhoare_wp { bwr_at = single k; bwr_uselet = uselet }) tc
  | FequivS _, (None | Some (Double _)) ->
      EcEquivWp.t_equiv_wp_full ~uselet (double k) tc
  | _ -> wp_error k tc

(* -------------------------------------------------------------------- *)
(* Dispatch on the goal kind only; each logic owns its surface-syntax
   handling. *)
let process_wp (cpos : pdocodegap1) (tc : tcenv1) =
  match (FApi.tc1_goal tc).f_node with
  | FhoareS   _ -> EcHoareWp.process_hoare_wp     cpos tc
  | FeHoareS  _ -> EcEHoareWp.process_ehoare_wp   cpos tc
  | FbdHoareS _ -> EcBdHoareWp.process_bdhoare_wp cpos tc
  | FequivS   _ -> EcEquivWp.process_equiv_wp     cpos tc
  | _ ->
      let cpos = omap (EcTyping.trans_dcodegap1 (FApi.tc1_env tc)) cpos in
      wp_error cpos tc
