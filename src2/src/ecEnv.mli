(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcDecl
open EcTypesmod

(* -------------------------------------------------------------------- *)
type preenv = {
  env_scope  : EcPath.path;
  env_root   : premc;
  env_comps  : (EcPath.path * premc) EcIdent.Mid.t
}

and premc = {
  mc_variables  : (EcPath.path * EcTypes.ty)        EcIdent.Map.t;
  mc_functions  : (EcPath.path * EcTypesmod.funsig) EcIdent.Map.t;
  mc_modules    : (EcPath.path * EcTypesmod.tymod)  EcIdent.Map.t;
  mc_modtypes   : (EcPath.path * EcTypesmod.tymod)  EcIdent.Map.t;
  mc_typedecls  : (EcPath.path * EcDecl.tydecl)     EcIdent.Map.t;
  mc_operators  : (EcPath.path * EcDecl.operator)   EcIdent.Map.t;
  mc_axioms     : (EcPath.path * EcDecl.axiom)      EcIdent.Map.t;
  mc_theories   : (EcPath.path * EcTypesmod.theory) EcIdent.Map.t;
  mc_components : unit EcIdent.Map.t;
}

(* -------------------------------------------------------------------- *)
type env = private preenv

val empty  : symbol -> EcIdent.t * env
val preenv : env -> preenv

(* -------------------------------------------------------------------- *)
exception LookupFailure of [`Path of EcPath.path | `QSymbol of qsymbol]

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
val root    : env -> EcPath.path
val enter   : symbol -> env -> EcIdent.t * env

(* -------------------------------------------------------------------- *)
module type S = sig
  type t

  val bind              : EcIdent.t -> t -> env -> env
  val bindall           : (EcIdent.t * t) list -> env -> env
  val lookup_by_path    : EcPath.path -> env -> t        (* full path *)
  val trylookup_by_path : EcPath.path -> env -> t option (* full path *)
  val lookup            : qsymbol -> env -> EcPath.path * t
  val trylookup         : qsymbol -> env -> (EcPath.path * t) option
  val exists            : qsymbol -> env -> bool
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

  val import : EcPath.path -> env -> env
  val export : EcPath.path -> env -> env
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
