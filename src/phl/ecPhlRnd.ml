(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcAst
open EcTypes

open EcMatching.Position
open EcCoreGoal

(* -------------------------------------------------------------------- *)
(* The [rnd] and [rndsem] rules live, one module per logic, in
   [rules/<logic>/]: each owns its parameter records, pure subgoal builder,
   recheckable proof-node, checker, derived forms and elaboration. This
   module only keeps the legacy entry points (adapters onto those modules,
   so external callers and this module's interface are unchanged) and the
   logic-agnostic dispatchers. *)

(* -------------------------------------------------------------------- *)
type bhl_infos_t = (ss_inv, ty -> ss_inv option, ty -> ss_inv) rnd_tac_info
type rnd_infos_t = (pformula, pformula option, pformula) rnd_tac_info
type mkbij_t     = EcTypes.ty -> EcTypes.ty -> ts_inv
type semrndpos   = (bool * codegap1) doption

(* -------------------------------------------------------------------- *)
let wp_equiv_disj_rnd = EcEquivRnd.t_equiv_rnd_onesided_last
let wp_equiv_rnd      = EcEquivRnd.t_equiv_rnd_last

(* -------------------------------------------------------------------- *)
let t_hoare_rnd = EcHoareRnd.t_hoare_rnd_last

let t_bdhoare_rnd (info : bhl_infos_t) =
  EcBdHoareRnd.(t_bdhoare_rnd_full { brr_info = info })

let t_equiv_rnd = EcEquivRnd.t_equiv_rnd_full

(* -------------------------------------------------------------------- *)
(* Dispatch on the goal kind only; each logic owns its surface-syntax
   handling. *)
let process_rnd
  (side     : side option)
  (pos      : psemrndpos option)
  (tac_info : rnd_infos_t)
  (tc       : tcenv1)
=
  match (FApi.tc1_goal tc).f_node with
  | FhoareS   _ -> EcHoareRnd.process_hoare_rnd     side pos tac_info tc
  | FeHoareS  _ -> EcEHoareRnd.process_ehoare_rnd   side pos tac_info tc
  | FbdHoareS _ -> EcBdHoareRnd.process_bdhoare_rnd side pos tac_info tc
  | FequivS   _ -> EcEquivRnd.process_equiv_rnd     side pos tac_info tc
  | _ -> tc_error !!tc "invalid arguments"

(* -------------------------------------------------------------------- *)
let process_rndsem ~reduce side pos (tc : tcenv1) =
  match (FApi.tc1_goal tc).f_node with
  | FhoareS   _ -> EcHoareRndSem.process_hoare_rndsem     ~reduce side pos tc
  | FbdHoareS _ -> EcBdHoareRndSem.process_bdhoare_rndsem ~reduce side pos tc
  | FequivS   _ -> EcEquivRndSem.process_equiv_rndsem     ~reduce side pos tc
  | _ ->
      (* The position is typed first, as before the migration: this reports
         a goal of the wrong kind, when it is not a program-logic one. *)
      ignore (EcLowPhlGoal.tc1_process_codegap1 tc (side, pos) : codegap1);
      tc_error !!tc "invalid arguments"
