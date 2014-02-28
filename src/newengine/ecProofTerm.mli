(* -------------------------------------------------------------------- *)
open EcLocation
open EcParsetree
open EcTypes
open EcFol
open EcEnv
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

(* Proof-terms typing *)
val process_pterm          : pt_env -> pformula fpattern_kind -> pt_ev
val process_pterm_arg      : pt_ev  -> fpattern_arg located -> pt_ev_arg
val process_pterm_args_app : pt_ev  -> fpattern_arg located list -> pt_ev
val process_full_pterm     : pt_env -> ffpattern -> pt_ev

(* Proof-terms tying in backward tactics *)
val tc_process_full_pterm : tcenv -> ffpattern -> pt_ev

(* Proof-terms manipulation *)
val apply_pterm_to_arg  : pt_ev -> pt_ev_arg -> pt_ev
val apply_pterm_to_hole : pt_ev -> pt_ev

(* pattern matching - raise [MatchFailure] on failure. *)
val pf_form_match : pt_env -> ptn:form -> form -> unit
val pf_unify      : pt_env -> ty -> ty -> unit

(* Proof-terms concretization, i.e. evmap/unienv resolution *)
val can_concretize : pt_env -> bool
val concretize     : pt_ev  -> proofterm * form
