(* -------------------------------------------------------------------- *)
open Symbols

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

val resolve : scope -> qsymbol -> Path.path option

module Op : sig
  type op = {
    op_path : Path.path;
    op_sig  : Types.ty list * Types.ty;
  }

  val resolve : scope -> qsymbol -> Types.ty list -> op option
end

module Ty : sig
  val resolve : scope -> qsymbol -> (int * Path.path) option
end
