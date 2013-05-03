(* -------------------------------------------------------------------- *)
open EcSymbols
open EcLocation
open EcParsetree

(* -------------------------------------------------------------------- *)
type scope

type proof_uc = {
  puc_name : string;
  puc_jdg :  EcBaseLogic.judgment_uc;
}

val empty   : scope
val path    : scope -> EcPath.path
val name    : scope -> symbol
val env     : scope -> EcEnv.env
val attop   : scope -> bool
val goal    : scope -> proof_uc list
val verbose : scope -> bool

module Op : sig
  (* [add scope op] type-checks the given *parsed* operator [op] in
   * scope [scope], and add it to it. Raises [DuplicatedNameInContext]
   * if a type with given name already exists. *)
  val add : scope -> poperator located -> scope
end

module Pred : sig
  (* [add scope op] type-checks the given *parsed* operator [op] in
   * scope [scope], and add it to it. Raises [DuplicatedNameInContext]
   * if a type with given name already exists. *)
  val add : scope -> ppredicate located -> scope
end

module Ax : sig
  (* [add scope op] type-checks the given *parsed* operator [op] in
   * scope [scope], and add it to it. Raises [DuplicatedNameInContext]
   * if an axiom with given name already exists. *)
  val add  : scope -> paxiom -> string option * scope
  val save : scope -> EcLocation.t -> string option * scope
end

module Ty : sig
  (* [add scope t] adds an abstract type with name [t] to scope
   * [scope]. Raises [DuplicatedNameInContext] if a type with
   * given name already exists. *)
  val add : scope -> (psymbol list * psymbol) located -> scope

  (* [define scope t body] adds a defined type with name [t] and body
   * [body] to scope [scope]. Can raise any exception triggered by the
   * type-checker or [DuplicatedNameInContext] in case a type with name
   * [t] already exists *)
  val define : scope -> (psymbol list * psymbol) located -> pty -> scope
end

module Mod : sig
  (* [add scope x m i] check the module [m] and add it to the scope
   * [scope] with name [x]. Can raise any exception triggered by the
   * type-checker or [DuplicatedNameInContext] in case a module with
   * name [x] already exists *)
  val add : scope -> symbol -> pmodule_expr -> scope
end

module ModType : sig
  (* [add scope x i] checks the module type [i] and add it to the
   * scope [scope] with name [x]. Can raise any exception triggered by
   * the type-checker or [DuplicatedNameInContext] in case a module
   * type with name [x] already exists *)
  val add : scope -> symbol -> pmodule_sig -> scope
end

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

  (* [clone scope (src, dst)] finds and clones theory [src] in
   * scope [scope]. Cloned theory name is [dst] if not None. If
   * [dst] is None, the basename of [src] is used as the cloned
   * theory name. *)
  val clone : scope -> theory_cloning -> scope

  (* FIXME: DOC *)
  val import_w3 : scope -> string list -> string -> w3_renaming list -> scope
end

module Tactic : sig
  val process : scope -> ptactics -> scope
end

module Prover : sig 
  val process     : scope -> pprover_infos -> scope
  val set_all     : scope -> scope 
  val set_default : scope -> int -> string list option -> scope
  val full_check  : scope -> scope
  val check_proof : scope -> bool -> scope
end
