(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2017 - Inria
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

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
type scope

type proof_uc = {
  puc_active : (proof_auc * proof_ctxt option) option;
  puc_cont   : proof_ctxt list * (EcEnv.env option);
  puc_init   : EcEnv.env;
}

and proof_auc = {
  puc_name   : symbol option;
  puc_mode   : bool option;
  puc_jdg    : proof_state;
  puc_flags  : pucflags;
  puc_crt    : EcDecl.axiom;
}

and proof_ctxt =
  (symbol option * EcDecl.axiom) * EcPath.path * EcEnv.env

and proof_state =
  PSNoCheck | PSCheck of EcCoreGoal.proof

and pucflags = {
  puc_nosmt : bool;
  puc_local : bool;
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
  val add : scope -> poperator located -> EcDecl.operator * scope
end

(* -------------------------------------------------------------------- *)
module Pred : sig
  val add : scope -> ppredicate located -> EcDecl.operator * scope
end

(* -------------------------------------------------------------------- *)
module Ax : sig
  type mode = [`WeakCheck | `Check | `Report]

  val add     : scope -> mode -> paxiom located -> symbol option * scope
  val save    : scope -> string option * scope
  val admit   : scope -> string option * scope
  val abort   : scope -> scope
  val realize : scope -> mode -> prealize located -> symbol option * scope
end

(* -------------------------------------------------------------------- *)
module Ty : sig
  val add : scope -> ptydname -> pqsymbol list -> scope

  val add_class    : scope -> ptypeclass located -> scope
  val add_instance : scope -> Ax.mode -> ptycinstance located -> scope
  val add_datatype : scope -> ptydname -> pdatatype -> scope
  val add_record   : scope -> ptydname -> precord -> scope

  val define : scope -> ptydname -> pty -> scope
end

(* -------------------------------------------------------------------- *)
module Mod : sig
  val add : scope -> pmodule_def -> scope
  val declare : scope -> pmodule_decl -> scope
end

(* -------------------------------------------------------------------- *)
module ModType : sig
  val add : scope -> symbol -> pmodule_sig -> scope
end

(* -------------------------------------------------------------------- *)
module Theory : sig
  open EcTheory

  exception TopScope

  (* [enter scope mode name] start a theory in scope [scope] with
   * name [name] and mode (abstract/concrete) [mode]. *)
  val enter : scope -> thmode -> symbol -> scope

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
  val require : scope -> (symbol * thmode) -> (scope -> scope) -> scope

  val add_clears : (pqsymbol option) list -> scope -> scope
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

  val process : scope -> Ax.mode -> ptactic list -> prinfos option * scope
  val proof   : scope -> Ax.mode -> bool -> scope
end

(* -------------------------------------------------------------------- *)
module Prover : sig
 type smt_options = {
    po_timeout    : int option;
    po_cpufactor  : int option;
    po_nprovers   : int option;
    po_provers    : string list option * (include_exclude * string) list;
    po_verbose    : int option;
    pl_all        : bool option;
    pl_max        : int option;
    pl_iterate    : bool option;
    pl_wanted     : EcProvers.hints option;
    pl_unwanted   : EcProvers.hints option;
  }

  val empty_options : smt_options

  val process     : scope -> pprover_infos -> scope
  val set_wrapper : scope -> string option -> scope

  val set_default : scope -> smt_options -> scope
  val full_check  : scope -> scope
  val check_proof : scope -> bool -> scope
end

(* -------------------------------------------------------------------- *)
module Notations : sig
  val add : scope -> pnotation located -> scope
  val add_abbrev : scope -> pabbrev located -> scope
end

(* -------------------------------------------------------------------- *)
module Auto : sig
  val addrw : scope -> (bool * pqsymbol * pqsymbol list) -> scope
  val addat : scope -> (bool * pqsymbol list) -> scope
end

(* -------------------------------------------------------------------- *)
module Cloning : sig
  val clone : scope -> Ax.mode -> theory_cloning -> scope
end

(* -------------------------------------------------------------------- *)
module Search : sig
  val search : scope -> pformula list -> unit
end
