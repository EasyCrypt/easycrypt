(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcTypesmod

(* -------------------------------------------------------------------- *)
type env

val empty : env

(* -------------------------------------------------------------------- *)
exception LookupFailure

(* -------------------------------------------------------------------- *)
type ebinding = [
  | `Variable  of EcTypes.ty
  | `Function  of funsig
  | `Operator  of operator
  | `Module    of tymod
  | `ModType   of tymod
  | `TypeDecl  of tydecl
  | `Theory    of theory
]

val bind1   : EcIdent.t * ebinding -> env -> env
val bindall : (EcIdent.t * ebinding) list -> env -> env
val root    : env -> EcPath.path option
val enter   : symbol -> env -> EcIdent.t * env

(* -------------------------------------------------------------------- *)
module type S = sig
  type t

  val bind      : EcIdent.t -> t -> env -> env
  val bindall   : (EcIdent.t * t) list -> env -> env
  val lookup    : qsymbol -> env -> EcPath.path * t
  val trylookup : qsymbol -> env -> (EcPath.path * t) option
end

(* -------------------------------------------------------------------- *)
module Var    : S with type t = EcTypes.ty
module Fun    : S with type t = funsig
module Op     : S with type t = operator
module Mod    : S with type t = tymod
module ModTy  : S with type t = tymod
module Theory : S with type t = theory

(* -------------------------------------------------------------------- *)
module Ty : sig
  include S with type t = tydecl

  val defined : EcPath.path -> env -> bool
  val unfold  : EcPath.path -> EcTypes.ty Parray.t -> env -> EcTypes.ty
end

(* -------------------------------------------------------------------- *)
module Ident : sig
  val lookup    : qsymbol -> env -> (EcPath.path * EcTypes.ty * [`Var | `Ctnt])
  val trylookup : qsymbol -> env -> (EcPath.path * EcTypes.ty * [`Var | `Ctnt]) option
end
