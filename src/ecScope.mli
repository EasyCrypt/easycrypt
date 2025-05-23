(* -------------------------------------------------------------------- *)
open EcSymbols
open EcLocation
open EcParsetree

(* -------------------------------------------------------------------- *)
exception HiScopeError of EcLocation.t option * string

val hierror : ?loc:EcLocation.t -> ('a, Format.formatter, unit, 'b) format4 -> 'a

(* -------------------------------------------------------------------- *)
exception ImportError of EcLocation.t option * symbol * exn

(* -------------------------------------------------------------------- *)
exception TopError of EcLocation.t * exn

val toperror_of_exn : ?gloc:EcLocation.t -> exn -> exn

(* -------------------------------------------------------------------- *)
type required_info = {
  rqd_name      : symbol;
  rqd_namespace : EcLoader.namespace option;
  rqd_kind      : EcLoader.kind;
  rqd_digest    : Digest.t;
  rqd_direct    : bool;
}

type required = required_info list

type scope

type proof_uc = {
  puc_active : (proof_auc * proof_ctxt option) option;
  puc_cont   : proof_ctxt list * (EcSection.scenv option);
  puc_init   : EcSection.scenv;
}

and proof_auc = {
  puc_name    : symbol option;
  puc_started : bool;
  puc_jdg     : proof_state;
  puc_flags   : pucflags;
  puc_crt     : EcDecl.axiom;
}

and proof_ctxt =
  (symbol option * EcDecl.axiom) * EcPath.path * EcSection.scenv

and proof_state =
  PSNoCheck | PSCheck of EcCoreGoal.proof

and pucflags = {
  puc_visibility : EcDecl.ax_visibility;
  puc_local      : bool;
}

(* -------------------------------------------------------------------- *)
val notify : scope -> EcGState.loglevel -> ('a, Format.formatter, unit, unit) format4 -> 'a

(* -------------------------------------------------------------------- *)
val empty  : EcGState.gstate -> scope
val gstate : scope -> EcGState.gstate
val freeze : scope -> scope
val path   : scope -> EcPath.path
val name   : scope -> symbol * EcTheory.thmode
val env    : scope -> EcEnv.env
val attop  : scope -> bool
val goal   : scope -> proof_auc option
val xgoal  : scope -> proof_uc option

(* Creates a scope that is identical to the supplied one except
 * that the environment and required theories are reset to the ones
 * from the prelude. *)
val for_loading : scope -> scope

type topmode = [`InProof | `InActiveProof | `InTop]

val check_state : topmode -> string -> scope -> unit

(* -------------------------------------------------------------------- *)
val dump_why3 : scope -> string -> unit

(* -------------------------------------------------------------------- *)
exception UnknownFlag of string

module Options : sig
  val set : scope -> string -> bool -> scope
  val get : scope -> string -> bool

  val set_implicits : scope -> bool -> scope
  val get_implicits : scope -> bool
end

(* -------------------------------------------------------------------- *)
module Op : sig
  val add : scope -> poperator located -> EcDecl.operator * string list * scope

  val add_opsem : scope -> pprocop located -> scope
end

(* -------------------------------------------------------------------- *)
module Pred : sig
  val add : scope -> ppredicate located -> EcDecl.operator * scope
end

(* -------------------------------------------------------------------- *)
module Ax : sig
  type proofmode = [`WeakCheck | `Check | `Report]

  val add     : scope -> proofmode -> paxiom located -> symbol option * scope
  val save    : scope -> string option * scope
  val admit   : scope -> string option * scope
  val abort   : scope -> scope
  val realize : scope -> proofmode -> prealize located -> symbol option * scope
end

(* -------------------------------------------------------------------- *)
module Ty : sig
  val add : scope -> ptydecl located -> scope

  val add_subtype : scope -> psubtype located -> scope
  val add_class    : scope -> ptypeclass located -> scope
  val add_instance : ?import:EcTheory.import -> scope -> Ax.proofmode -> ptycinstance located -> scope
end

(* -------------------------------------------------------------------- *)
module Mod : sig
  val add : scope -> pmodule_def_or_decl -> scope
  val declare : scope -> pmodule_decl -> scope
  val import : scope -> pmsymbol located -> scope
end

(* -------------------------------------------------------------------- *)
module ModType : sig
  val add : scope -> pinterface -> scope
end

(* -------------------------------------------------------------------- *)
module Theory : sig
  open EcTheory

  exception TopScope

  (* [update_with_required dst src] updates [dst] with the required
   * theories of [src] *)
  val update_with_required : dst:scope -> src:scope -> scope

  (* [enter scope mode name] start a theory in scope [scope] with
   * name [name] and mode (abstract/concrete) [mode]. *)
  val enter : scope -> thmode -> symbol -> EcTypes.is_local -> scope

  (* [exit scope] close and finalize the top-most theory and returns
   * its name. Raises [TopScope] if [scope] has not super scope. *)
  val exit :
       ?pempty:[`ClearOnly | `Full | `No]
    -> ?clears:(pqsymbol option) list
    -> scope -> symbol * scope

  (* [import scope name] find and import theory [name] in scope
   * [scope]. Raise [LookupFailure] if theory [name] cannot be
   * found. *)
  val import : scope -> qsymbol -> scope

  (* [export scope name] marks the theory [name] to by exported
   *  by current theory in scope [scope]. Raise [LookupFailure] if
   *  theory [theory] cannot be found. *)
  val export : scope -> qsymbol -> scope

  (* [require scope name loader] requires theory [name] using
   * loader [loader] in scope [scope]. [loader] is called on
   * the initial scope and is in charge of processing the required
   * theory. *)
  val require : scope -> (required_info * thmode) -> (scope -> scope) -> scope

  val add_clears : (pqsymbol option) list -> scope -> scope

  val required : scope -> required

  (* [alias scope (name, thname)] create a theory alias [name] to
   * [thname] *)
  val alias : scope -> ?import:EcTheory.import -> psymbol * pqsymbol -> scope
end

(* -------------------------------------------------------------------- *)
module Section : sig
  val enter : scope -> psymbol option -> scope
  val exit  : scope -> psymbol option-> scope
end

(* -------------------------------------------------------------------- *)
module Tactics : sig
  open EcCoreGoal

  type prinfos = proofenv * (handle * handle list)
  type proofmode = Ax.proofmode

  val process : scope -> proofmode -> ptactic list -> prinfos option * scope
  val proof   : scope -> scope
end

(* -------------------------------------------------------------------- *)
module Prover : sig
 type smt_options = {
    po_timeout    : int option;
    po_cpufactor  : int option;
    po_nprovers   : int option;
    po_provers    : string list option * (include_exclude * string) list;
    po_quorum     : int option;
    po_verbose    : int option;
    pl_all        : bool option;
    pl_max        : int option;
    pl_iterate    : bool option;
    pl_wanted     : EcProvers.hints option;
    pl_unwanted   : EcProvers.hints option;
    pl_dumpin     : string located option;
    pl_selected   : bool option;
    gn_debug      : bool option;
  }

  val empty_options : smt_options

  val process     : scope -> pprover_infos -> scope

  val set_default : scope -> smt_options -> scope
  val full_check  : scope -> scope
  val check_proof : scope -> bool -> scope

  val pprover_infos_to_prover_infos :
       EcEnv.env
    -> EcProvers.prover_infos
    -> pprover_infos
    -> EcProvers.prover_infos
end

(* -------------------------------------------------------------------- *)
module Notations : sig
  val add : scope -> pnotation located -> scope
  val add_abbrev : scope -> pabbrev located -> scope
end

(* -------------------------------------------------------------------- *)
module Auto : sig
  val add_rw   : scope -> local:EcTypes.is_local -> base:pqsymbol -> pqsymbol list -> scope
  val add_hint : scope -> phint -> scope
end

(*-------------------------------------------------------------------- *)
module Reduction : sig
  val add_reduction : scope -> puserred -> scope
end

(* -------------------------------------------------------------------- *)
module Cloning : sig
  val clone : scope -> Ax.proofmode -> theory_cloning -> scope
end

(* -------------------------------------------------------------------- *)
module Search : sig
  val search : scope -> pformula list -> unit
  val locate : scope -> pqsymbol -> unit
end
