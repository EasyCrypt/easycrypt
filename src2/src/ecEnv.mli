(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcDecl
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
exception UnknownPath of EcPath.path

module type S = sig
  type t

  val bind        : EcIdent.t -> t -> env -> env
  val bindall     : (EcIdent.t * t) list -> env -> env
  val lookup_p    : EcPath.path -> env -> t        (* full path *)
  val trylookup_p : EcPath.path -> env -> t option (* full path *)
  val lookup      : qsymbol -> env -> EcPath.path * t
  val trylookup   : qsymbol -> env -> (EcPath.path * t) option
  val exists      : qsymbol -> env -> bool
end

(* -------------------------------------------------------------------- *)
module Var    : S with type t = EcTypes.ty
module Fun    : S with type t = funsig
module Ax     : S with type t = axiom
module Mod    : S with type t = tymod
module ModTy  : S with type t = tymod

(* -------------------------------------------------------------------- *)
module Theory : sig
  include S with type t = theory

  val use    : EcPath.path -> env -> env
  val use_qs : qsymbol -> env -> EcPath.path * env
  val import : qsymbol -> env -> env
end

(* -------------------------------------------------------------------- *)
module Op : sig
  include S with type t = operator

  val all : qsymbol -> env -> (EcPath.path * t) list
end

(* -------------------------------------------------------------------- *)
module Ty : sig
  include S with type t = tydecl

  val defined : EcPath.path -> env -> bool
  val unfold  : EcPath.path -> EcTypes.ty list -> env -> EcTypes.ty
end

(* -------------------------------------------------------------------- *)
module Ident : sig
  type idlookup_t = [`Var | `Ctnt of operator]

  val lookup    : 
      qsymbol -> env -> (EcPath.path * EcTypes.ty option * idlookup_t)
  val trylookup : 
      qsymbol -> env -> (EcPath.path * EcTypes.ty option * idlookup_t) option
end
