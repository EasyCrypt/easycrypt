(* Copyright (c) - 2012-2014 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-B license *)

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
type evmap = form EcMatching.evmap

type pt_env = {
  pte_pe : proofenv;         (* proofenv of this proof-term *)
  pte_hy : LDecl.hyps;       (* local context *)
  pte_ue : EcUnify.unienv;   (* unification env. *)
  pte_ev : evmap ref;        (* metavar env. *)
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
val trans_pterm_arg_value : pt_env -> ?name:symbol -> fpattern_arg located -> pt_ev_arg
val trans_pterm_arg_mod   : pt_env -> fpattern_arg located -> pt_ev_arg
val trans_pterm_arg_mem   : pt_env -> fpattern_arg located -> pt_ev_arg

(* Proof-terms typing *)
val process_pterm_cut             : prcut:('a -> form) -> pt_env -> 'a fpattern_kind -> pt_ev
val process_pterm                 : pt_env -> pformula fpattern_kind -> pt_ev
val process_pterm_arg             : pt_ev  -> fpattern_arg located -> pt_ev_arg
val process_pterm_args_app        : pt_ev  -> fpattern_arg located list -> pt_ev
val process_full_pterm_cut        : prcut:('a -> form) -> pt_env -> 'a fpattern -> pt_ev
val process_full_pterm            : pt_env -> ffpattern -> pt_ev
val process_full_closed_pterm_cut : prcut:('a -> form) -> pt_env -> 'a fpattern -> proofterm * form
val process_full_closed_pterm     : pt_env -> ffpattern -> proofterm * form

(* Proof-terms typing in backward tactics *)
val tc1_process_pterm_cut             : prcut:('a -> form) -> tcenv1 -> 'a fpattern_kind -> pt_ev
val tc1_process_pterm                 : tcenv1 -> pformula fpattern_kind -> pt_ev
val tc1_process_full_pterm_cut        : prcut:('a -> form) -> tcenv1 -> 'a fpattern -> pt_ev
val tc1_process_full_pterm            : tcenv1 -> ffpattern -> pt_ev
val tc1_process_full_closed_pterm_cut : prcut:('a -> form) -> tcenv1 -> 'a fpattern -> proofterm * form
val tc1_process_full_closed_pterm     : tcenv1 -> ffpattern -> proofterm * form

(* Proof-terms manipulation *)
val check_pterm_arg     : pt_env -> EcIdent.t * gty -> form -> pt_ev_arg_r -> form * pt_arg
val apply_pterm_to_arg  : pt_ev -> pt_ev_arg -> pt_ev
val apply_pterm_to_hole : pt_ev -> pt_ev

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

val ptenv : proofenv -> LDecl.hyps -> (EcUnify.unienv * evmap) -> pt_env
val copy  : pt_env -> pt_env

(* Proof-terms construction from components *)
val pt_of_hyp    : proofenv -> LDecl.hyps -> EcIdent.t -> pt_ev
val pt_of_global : proofenv -> LDecl.hyps -> EcPath.path -> ty list -> pt_ev
val pt_of_uglobal: proofenv -> LDecl.hyps -> EcPath.path -> pt_ev

(* -------------------------------------------------------------------- *)
val ffpattern_of_genpattern : LDecl.hyps -> genpattern -> ffpattern option
