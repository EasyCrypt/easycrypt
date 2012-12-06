(* -------------------------------------------------------------------- *)
open EcSymbols
open EcParsetree

(* -------------------------------------------------------------------- *)
module Context : sig
  type symbol = string

  type 'a context

  exception DuplicatedNameInContext of string
  exception UnboundName of string

  val empty   : unit -> 'a context
  val bind    : symbol -> 'a -> 'a context -> 'a context
  val rebind  : symbol -> 'a -> 'a context -> 'a context
  val exists  : symbol -> 'a context -> bool
  val lookup  : symbol -> 'a context -> 'a option
  val iter    : (symbol -> 'a -> unit) -> 'a context -> unit
  val fold    : ('b -> symbol -> 'a -> 'b) -> 'b -> 'a context -> 'b
  val tolist  : 'a context -> (symbol * 'a) list
end

(* -------------------------------------------------------------------- *)
type scope

val initial : symbol -> scope
val name    : scope -> EcIdent.t
val env     : scope -> EcEnv.env
val attop   : scope -> bool

module Op : sig
  (* [add scope op] type-checks the given *parsed* operator [op] in
   * scope [scope], and add it to it. Raises [DuplicatedNameInContext]
   * if a type with given name already exists. *)
  val add : scope -> poperator -> scope
end

module Pred : sig
  (* [add scope op] type-checks the given *parsed* operator [op] in
   * scope [scope], and add it to it. Raises [DuplicatedNameInContext]
   * if a type with given name already exists. *)
  val add : scope -> ppredicate -> scope
end

module Ax : sig

  (* [add scope op] type-checks the given *parsed* operator [op] in
   * scope [scope], and add it to it. Raises [DuplicatedNameInContext]
   * if an axiom with given name already exists. *)
  val add : scope -> paxiom -> scope
end

module Ty : sig
  (* [add scope t] adds an abstract type with name [t] to scope
   * [scope]. Raises [DuplicatedNameInContext] if a type with
   * given name already exists. *)
  val add : scope -> (symbol list * symbol) -> scope

  (* [define scope t body] adds a defined type with name [t] and body
   * [body] to scope [scope]. Can raise any exception triggered by the
   * type-checker or [DuplicatedNameInContext] in case a type with name
   * [t] already exists *)
  val define : scope -> (symbol list * symbol) -> pty -> scope
end

module Mod : sig
  (* [add scope x m] chekc the module [n] and add it to the scope
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
  val add : scope -> symbol -> pmodule_type -> scope
end

module Theory : sig
  exception TopScope

  (* [enter scope name] start a (sub-)theory in scope [scope] with
   * name [name]. *)
  val enter : scope -> symbol -> scope

  (* [exit scope] close and finalize the top-most theory and returns
   * its name. Raises [TopScope] if [scope] has not super scope. *)
  val exit  : scope -> EcIdent.t * scope

  (* [import scope name] find and import theory [name] in scope
   * [scope]. Raise [LookupFailure] if theory [name] cannot be
   * found. *)
  val import : scope -> qsymbol -> scope
end
