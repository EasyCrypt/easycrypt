(* -------------------------------------------------------------------- *)
open Symbols
open Typesmod

(* -------------------------------------------------------------------- *)
type env

val empty : env

(* -------------------------------------------------------------------- *)
exception LookupFailure

(* -------------------------------------------------------------------- *)
module type S = sig
  type t

  val bind      : Ident.t -> t -> env -> env
  val bindall   : (Ident.t * t) list -> env -> env
  val lookup    : qsymbol -> env -> Path.path * t
  val trylookup : qsymbol -> env -> (Path.path * t) option
end

(* -------------------------------------------------------------------- *)
module Var : S with type t = Types.ty
module Fun : S with type t = funsig
module Mod : S with type t = tymod
module Ty  : S with type t = tydecl
module Op  : S with type t = operator

(* -------------------------------------------------------------------- *)
type ebinding = [
  | `Variable  of Types.ty
  | `Function  of funsig
  | `Module    of tymod
]

val bind1   : Ident.t * ebinding -> env -> env
val bindall : (Ident.t * ebinding) list -> env -> env
