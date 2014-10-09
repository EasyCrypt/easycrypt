(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2014 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcSymbols
open EcLocation
open EcParsetree

(* -------------------------------------------------------------------- *)
exception HiScopeError of EcLocation.t option * string

val hierror : ?loc:EcLocation.t -> ('a, Format.formatter, unit, 'b) format4 -> 'a

(* -------------------------------------------------------------------- *)
type scope

type proof_uc = {
  puc_active : proof_auc option;
  puc_cont   : proof_ctxt list * (EcEnv.env option);
}

and proof_auc = {
  puc_name   : string;
  puc_mode   : bool option;
  puc_jdg    : proof_state;
  puc_flags  : pucflags;
  puc_crt    : EcDecl.axiom;
}

and proof_ctxt = (symbol * EcDecl.axiom) * EcPath.path * EcEnv.env

and proof_state = PSNoCheck | PSCheck of EcCoreGoal.proof

and pucflags = {
  puc_nosmt : bool;
  puc_local : bool;
}

(* -------------------------------------------------------------------- *)
val notify : scope -> EcGState.loglevel -> ('a, unit, string, unit) format4 -> 'a

(* -------------------------------------------------------------------- *)
val empty   : EcGState.gstate -> scope
val gstate  : scope -> EcGState.gstate
val path    : scope -> EcPath.path
val name    : scope -> symbol
val env     : scope -> EcEnv.env
val attop   : scope -> bool
val goal    : scope -> proof_auc option
val xgoal   : scope -> proof_uc option

type topmode = [`InProof | `InActiveProof | `InTop]

val check_state : topmode -> string -> scope -> unit

(* -------------------------------------------------------------------- *)
module Op : sig
  val add : scope -> poperator located -> scope
end

(* -------------------------------------------------------------------- *)
module Pred : sig
  val add : scope -> ppredicate located -> scope
end

(* -------------------------------------------------------------------- *)
module Ax : sig
  type mode = [`WeakCheck | `Check]

  val add  : scope -> mode -> paxiom located -> string option * scope
  val save : scope -> EcLocation.t -> string option * scope

  val activate : scope -> EcParsetree.pqsymbol -> scope
end

(* -------------------------------------------------------------------- *)
module Ty : sig
  type tydname = (ptyparams * psymbol) located

  val add : scope -> tydname -> pqsymbol list -> scope

  val add_class    : scope -> ptypeclass located -> scope
  val add_instance : scope -> Ax.mode -> ptycinstance located -> scope
  val add_datatype : scope -> tydname -> pdatatype -> scope
  val add_record   : scope -> tydname -> precord -> scope

  val define : scope -> tydname -> pty -> scope
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
  exception TopScope

  (* [enter scope name] start a theory in scope [scope] with
   * name [name]. *)
  val enter : scope -> symbol -> scope

  (* [exit scope] close and finalize the top-most theory and returns
   * its name. Raises [TopScope] if [scope] has not super scope. *)
  val exit  : scope -> symbol * scope

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
  val require : scope -> symbol -> (scope -> scope) -> scope

  (* FIXME: DOC *)
  val import_w3 : scope -> string list -> string -> w3_renaming list -> scope
end

(* -------------------------------------------------------------------- *)
module Section : sig
  val enter : scope -> psymbol option -> scope
  val exit  : scope -> psymbol option-> scope
end

(* -------------------------------------------------------------------- *)
module Tactics : sig
  val process : scope -> Ax.mode -> ptactic list -> scope
  val proof   : scope -> Ax.mode -> bool -> scope
end

(* -------------------------------------------------------------------- *)
module Prover : sig
  val process     : scope -> pprover_infos -> scope
  val set_wrapper : scope -> string option -> scope
  val set_all     : scope -> scope
  val set_default : scope -> timeout:int -> nprovers:int -> string list option -> scope
  val full_check  : scope -> scope
  val check_proof : scope -> bool -> scope
end

(* -------------------------------------------------------------------- *)
module Extraction : sig
  val process :
    scope -> (string option * toextract list * withextract list) -> scope
end

(* -------------------------------------------------------------------- *)
module BaseRw : sig
  val process_addrw : scope -> (pqsymbol * pqsymbol list) -> scope
end
