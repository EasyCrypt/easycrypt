(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcLocation
open EcSymbols
open EcParsetree
open EcTypes
open EcFol
open EcEnv
open EcMatching
open EcCoreGoal

(* -------------------------------------------------------------------- *)
type pt_env = {
  pte_pe : proofenv;         (* proofenv of this proof-term *)
  pte_hy : LDecl.hyps;       (* local context *)
  pte_ue : EcUnify.unienv;   (* unification env. *)
  pte_ev : mevmap ref;       (* metavar env. *)
}

type pt_ev = {
  ptev_env : pt_env;
  ptev_pt  : proofterm;
  ptev_ax  : form;
}

type pt_ev_arg = {
  ptea_env : pt_env;
  ptea_arg : pt_ev_arg_r;
}

and pt_ev_arg_r =
| PVAFormula of EcFol.form
| PVAMemory  of EcMemory.memory
| PVAModule  of (EcPath.mpath * EcModules.module_sig)
| PVASub     of pt_ev

(* Arguments typing *)
val trans_pterm_arg_value : pt_env -> ?name:symbol -> ppt_arg located -> pt_ev_arg
val trans_pterm_arg_mod   : pt_env -> ppt_arg located -> pt_ev_arg
val trans_pterm_arg_mem   : pt_env -> ?name:symbol -> ppt_arg located -> pt_ev_arg

(* Proof-terms typing *)
val process_pterm_cut             : prcut:('a -> form) -> pt_env -> 'a ppt_head -> pt_ev
val process_pterm                 : pt_env -> pformula ppt_head -> pt_ev
val process_pterm_arg             : pt_ev  -> ppt_arg located -> pt_ev_arg
val process_pterm_args_app        : pt_ev  -> ppt_arg located list -> pt_ev
val process_full_pterm_cut        : prcut:('a -> form) -> pt_env -> 'a gppterm -> pt_ev
val process_full_pterm            : ?implicits:bool -> pt_env -> ppterm -> pt_ev
val process_full_closed_pterm_cut : prcut:('a -> form) -> pt_env -> 'a gppterm -> proofterm * form
val process_full_closed_pterm     : pt_env -> ppterm -> proofterm * form

(* Proof-terms typing in backward tactics *)
val tc1_process_pterm_cut             : prcut:('a -> form) -> tcenv1 -> 'a ppt_head -> pt_ev
val tc1_process_pterm                 : tcenv1 -> pformula ppt_head -> pt_ev
val tc1_process_full_pterm_cut        : prcut:('a -> form) -> tcenv1 -> 'a gppterm -> pt_ev
val tc1_process_full_pterm            : ?implicits:bool -> tcenv1 -> ppterm -> pt_ev
val tc1_process_full_closed_pterm_cut : prcut:('a -> form) -> tcenv1 -> 'a gppterm -> proofterm * form
val tc1_process_full_closed_pterm     : tcenv1 -> ppterm -> proofterm * form

(* Proof-terms manipulation *)
val check_pterm_arg      : pt_env -> EcIdent.t * gty -> form -> pt_ev_arg_r -> form * pt_arg
val apply_pterm_to_arg   : pt_ev -> pt_ev_arg -> pt_ev
val apply_pterm_to_arg_r : pt_ev -> pt_ev_arg_r -> pt_ev
val apply_pterm_to_hole  : pt_ev -> pt_ev

(* pattern matching - raise [MatchFailure] on failure. *)
val pf_form_match     : pt_env -> ?mode:fmoptions -> ptn:form -> form -> unit
val pf_unify          : pt_env -> ty -> ty -> unit
val pf_find_occurence : pt_env -> ptn:form -> form -> unit

val pattern_form :
     ?name:symbol -> LDecl.hyps -> ptn:form -> form
  -> EcIdent.t * form

(* Proof-terms concretization, i.e. evmap/unienv resolution *)
type cptenv

val can_concretize  : pt_env -> bool
val concretize_env  : pt_env -> cptenv
val concretize      : pt_ev  -> proofterm * form
val concretize_form : pt_env -> form -> form

val concretize_e_form : cptenv -> form -> form
val concretize_e_arg  : cptenv -> pt_arg -> pt_arg

(* PTEnv constructor *)
val ptenv_of_penv : LDecl.hyps -> proofenv -> pt_env

val ptenv : proofenv -> LDecl.hyps -> (EcUnify.unienv * mevmap) -> pt_env
val copy  : pt_env -> pt_env

(* Proof-terms construction from components *)
val pt_of_hyp    : proofenv -> LDecl.hyps -> EcIdent.t -> pt_ev
val pt_of_global : proofenv -> LDecl.hyps -> EcPath.path -> ty list -> pt_ev
val pt_of_uglobal: proofenv -> LDecl.hyps -> EcPath.path -> pt_ev

val pt_of_global_r : pt_env -> EcPath.path -> ty list -> pt_ev

(* -------------------------------------------------------------------- *)
val ffpattern_of_genpattern : LDecl.hyps -> genpattern -> ppterm option

(* -------------------------------------------------------------------- *)
type prept = [
  | `Hy   of EcIdent.t 
  | `G    of EcPath.path * ty list 
  | `UG   of EcPath.path
  | `App  of prept * prept_arg list
]

and prept_arg =  [
  | `F   of form
  | `Mem of EcMemory.memory
  | `Mod of (EcPath.mpath * EcModules.module_sig)
  | `Sub of prept
  | `H_
]

val pt_of_prept: tcenv1 -> prept -> pt_ev
