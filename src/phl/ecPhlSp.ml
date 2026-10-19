(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcAst
open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* The [sp] rules live, one module per logic, in [rules/<logic>/] (the
   strongest-postcondition calculus they share is [EcPlSp]). This module
   only keeps the legacy entry point and the logic-agnostic dispatchers,
   which route on the goal kind and on the shape of the position (single
   for hoare / bdhoare, a pair for equiv). *)

(* -------------------------------------------------------------------- *)
let as_single = function Single i -> i | Double _ -> assert false
let as_double = function Double i -> i | Single _ -> assert false

(* -------------------------------------------------------------------- *)
let t_sp_unsupported (pos : 'a doption option) (tc : tcenv1) =
  match pos with
  | Some (Single _) ->
      tc_error_noXhl ~kinds:[`Hoare `Stmt; `PHoare `Stmt] !!tc
  | Some (Double _) ->
      tc_error_noXhl ~kinds:[`Equiv `Stmt] !!tc
  | None ->
      tc_error_noXhl ~kinds:(hlkinds_Xhl_r `Stmt) !!tc

(* -------------------------------------------------------------------- *)
let t_sp (pos : EcMatching.Position.codegap1 doption option) (tc : tcenv1) =
  match (FApi.tc1_goal tc).f_node, pos with
  | FhoareS _, (None | Some (Single _)) ->
      EcHoareSp.t_hoare_sp_prefix (omap as_single pos) tc
  | FbdHoareS _, (None | Some (Single _)) ->
      EcBdHoareSp.t_bdhoare_sp_prefix (omap as_single pos) tc
  | FequivS _, (None | Some (Double _)) ->
      EcEquivSp.t_equiv_sp_prefix (omap as_double pos) tc
  | _ ->
      t_sp_unsupported pos tc

(* -------------------------------------------------------------------- *)
(* [process_sp gap]: splits the statement at [gap]; instructions after the
   gap are kept, sp is applied to instructions before the gap. *)
let process_sp (pos : pcodegap1 doption option) (tc : tcenv1) =
  match (FApi.tc1_goal tc).f_node, pos with
  | FhoareS _, (None | Some (Single _)) ->
      EcHoareSp.process_hoare_sp (omap as_single pos) tc
  | FbdHoareS _, (None | Some (Single _)) ->
      EcBdHoareSp.process_bdhoare_sp (omap as_single pos) tc
  | FequivS _, (None | Some (Double _)) ->
      EcEquivSp.process_equiv_sp (omap as_double pos) tc
  | _ ->
      (* The position is still typed first, as before the migration, so
         that its errors take precedence. *)
      let env = FApi.tc1_env tc in
      t_sp_unsupported (omap (EcTyping.trans_dcodegap1 env) pos) tc
