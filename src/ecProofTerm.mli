(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
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
type apperror =
  | AE_WrongArgKind of (argkind * argkind)
  | AE_CannotInfer
  | AE_CannotInferMod
  | AE_NotFunctional
  | AE_InvalidArgForm     of invalid_arg_form
  | AE_InvalidArgMod
  | AE_InvalidArgProof    of (form * form)
  | AE_InvalidArgModRestr of EcTyping.restriction_error

and argkind = [`Form | `Mem | `Mod | `PTerm]

and invalid_arg_form =
  | IAF_Mismatch of (ty * ty)
  | IAF_TyError of env * EcTyping.tyerror

type pterror = (LDecl.hyps * EcUnify.unienv * mevmap) * apperror

exception ProofTermError of pterror

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
val process_pterm_cut
  : prcut:('a -> form) -> pt_env -> 'a ppt_head -> pt_ev
val process_pterm
  : pt_env -> (pformula option) ppt_head -> pt_ev
val process_pterm_arg
   : ?implicits:bool -> pt_ev  -> ppt_arg located -> pt_ev_arg
val process_pterm_args_app
  :  ?implicits:bool -> ?ip:(bool list) -> pt_ev  -> ppt_arg located list
  -> pt_ev * bool list
val process_full_pterm_cut
  : prcut:('a -> form) -> pt_env -> 'a gppterm -> pt_ev
val process_full_pterm
  : ?implicits:bool -> pt_env -> ppterm -> pt_ev
val process_full_closed_pterm_cut
  : prcut:('a -> form) -> pt_env -> 'a gppterm -> proofterm * form
val process_full_closed_pterm
  : pt_env -> ppterm -> proofterm * form

(* Proof-terms typing in backward tactics *)
val tc1_process_pterm_cut
 : prcut:('a -> form) -> tcenv1 -> 'a ppt_head -> pt_ev
val tc1_process_pterm
 : tcenv1 -> (pformula option) ppt_head -> pt_ev
val tc1_process_full_pterm_cut
 : prcut:('a -> form) -> tcenv1 -> 'a gppterm -> pt_ev
val tc1_process_full_pterm
 : ?implicits:bool -> tcenv1 -> ppterm -> pt_ev
val tc1_process_full_closed_pterm_cut
 : prcut:('a -> form) -> tcenv1 -> 'a gppterm -> proofterm * form
val tc1_process_full_closed_pterm
 : tcenv1 -> ppterm -> proofterm * form

(* Proof-terms manipulation *)
val check_pterm_arg :
    ?loc:EcLocation.t
  -> pt_env
  -> EcIdent.t * gty
  -> form
  -> pt_ev_arg_r
 -> form * pt_arg

val apply_pterm_to_arg   : ?loc:EcLocation.t -> pt_ev -> pt_ev_arg -> pt_ev
val apply_pterm_to_arg_r : ?loc:EcLocation.t -> pt_ev -> pt_ev_arg_r -> pt_ev
val apply_pterm_to_hole  : ?loc:EcLocation.t -> pt_ev -> pt_ev
val apply_pterm_to_holes : ?loc:EcLocation.t -> int -> pt_ev -> pt_ev

(* pattern matching - raise [MatchFailure] on failure. *)
val pf_form_match : pt_env -> ?mode:fmoptions -> ptn:form -> form -> unit
val pf_unify : pt_env -> ty -> ty -> unit

(* pattern matching - raise [FindOccFailure] on failure. *)
exception FindOccFailure of [`MatchFailure | `IncompleteMatch]

type occmode = {
  k_keyed : bool;
  k_conv  : bool;
}

val pf_find_occurence :
  pt_env -> ?occmode:occmode -> ptn:form -> form -> form * occmode

val pf_find_occurence_lazy :
  pt_env -> ?modes:occmode list -> ptn:form -> form -> form * occmode

(* -------------------------------------------------------------------- *)
val pattern_form :
     ?name:symbol -> LDecl.hyps -> ptn:form -> form
  -> EcIdent.t * form

(* Proof-terms concretization, i.e. evmap/unienv resolution *)
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
  | `HD   of handle
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

(* -------------------------------------------------------------------- *)
module Prept : sig
  val (@)   : prept -> prept_arg list -> prept

  val hyp   : EcIdent.t -> prept
  val glob  : EcPath.path -> ty list -> prept
  val uglob : EcPath.path -> prept
  val hdl   : handle -> prept

  val aform : form -> prept_arg
  val amem  : EcMemory.memory -> prept_arg
  val amod  : EcPath.mpath -> EcModules.module_sig -> prept_arg
  val asub  : prept -> prept_arg
  val h_    : prept_arg
  val ahyp  : EcIdent.t -> prept_arg
  val ahdl  : handle -> prept_arg
end
