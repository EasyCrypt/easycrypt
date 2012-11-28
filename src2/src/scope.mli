(* -------------------------------------------------------------------- *)
open Symbols
open Parsetree

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
val name    : scope -> symbol
val env     : scope -> Env.env

module Op : sig
  (* Possible exceptions when checking/adding an operator *)
  type operror =
  | OpE_DuplicatedTypeVariable

  exception OpError of operror

  val operror : operror -> 'a

  (* [add scope op] type-checks the given *parsed* operator [op] in
   * scope [scope], and add it to it. Raises [DuplicatedNameInContext]
   * if a type with given name already exists. *)
  val add : scope -> poperator -> scope
end

module Ty : sig
  (* [add scope t] adds an abstract type with name [t] to scope
   * [scope]. Raises [DuplicatedNameInContext] if a type with
   * given name already exists. *)
  val add : scope -> symbol -> scope
end
