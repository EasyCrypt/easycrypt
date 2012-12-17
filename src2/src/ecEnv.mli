(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcDecl
open EcTypesmod

(* -------------------------------------------------------------------- *)
type preenv = private {
  env_scope  : EcPath.path;
  env_root   : premc;
  env_comps  : (EcPath.path * premc) EcIdent.Mid.t;
  env_w3     : EcWhy3.env;
  env_rb     : EcWhy3.rebinding;        (* in reverse order *)
  env_item   : theory_item list         (* in reverse order *)
}

and premc = private {
  mc_variables  : (EcPath.path * varbind)           EcIdent.Map.t;
  mc_functions  : (EcPath.path * EcTypesmod.funsig) EcIdent.Map.t;
  mc_modules    : (EcPath.path * EcTypesmod.tymod)  EcIdent.Map.t;
  mc_modtypes   : (EcPath.path * EcTypesmod.tymod)  EcIdent.Map.t;
  mc_typedecls  : (EcPath.path * EcDecl.tydecl)     EcIdent.Map.t;
  mc_operators  : (EcPath.path * EcDecl.operator)   EcIdent.Map.t;
  mc_axioms     : (EcPath.path * EcDecl.axiom)      EcIdent.Map.t;
  mc_theories   : (EcPath.path * EcTypesmod.theory) EcIdent.Map.t;
  mc_components : unit EcIdent.Map.t;
}

and varbind = {
  vb_type  : EcTypes.ty;
  vb_local : bool;
}

(* -------------------------------------------------------------------- *)
type env = preenv

val preenv  : env -> preenv
val initial : env
val root    : env -> EcPath.path

(* -------------------------------------------------------------------- *)
exception LookupFailure of [`Path of EcPath.path | `QSymbol of qsymbol]

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
module Fun   : S with type t = funsig
module Ax    : S with type t = axiom
module ModTy : S with type t = tymod

(* -------------------------------------------------------------------- *)
module Var : sig
  include S with type t = varbind

  val bind : EcIdent.t -> EcTypes.ty -> ?local:bool -> env -> env
  val bindall : (EcIdent.t * EcTypes.ty) list -> ?local:bool -> env -> env
end

(* -------------------------------------------------------------------- *)
module Mod : sig
  type t = module_expr

  val bind_s : EcIdent.t -> tymod -> env -> env
  val bindall_s : (EcIdent.t * tymod) list -> env -> env
  val bind : EcIdent.t -> t -> env -> env
  val bindall : (EcIdent.t * t) list -> env -> env
  val lookup_by_path : EcPath.path -> env -> tymod
  val lookup : EcSymbols.qsymbol -> env -> EcPath.path * EcTypesmod.tymod
  val trylookup_by_path : EcPath.path -> env -> EcTypesmod.tymod option
  val trylookup : EcSymbols.qsymbol -> env -> (EcPath.path * EcTypesmod.tymod) option
  val exists : EcSymbols.qsymbol -> env -> bool
end

(* -------------------------------------------------------------------- *)
type comp_th

val theory_of_comp_th : comp_th -> theory

module Theory : sig
  type t = comp_th

  val bind : EcIdent.t -> t -> env -> env
  val bindall : (EcIdent.t * t) list -> env -> env
  val lookup_by_path : EcPath.path -> env -> theory
  val lookup : EcSymbols.qsymbol -> env -> EcPath.path * theory
  val trylookup_by_path : EcPath.path -> env -> theory option
  val trylookup : EcSymbols.qsymbol -> env -> (EcPath.path * theory) option
  val exists : EcSymbols.qsymbol -> env -> bool
  val import : EcPath.path -> env -> env
  val export : EcPath.path -> env -> env
  val require : EcIdent.t -> theory -> env -> env
  val enter : EcSymbols.symbol -> env -> EcIdent.t * env
  val close : env -> comp_th
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
  type idlookup_t = [`Var of bool | `Ctnt of operator]

  val lookup    : 
      qsymbol -> env -> (EcPath.path * EcTypes.ty option * idlookup_t)
  val trylookup : 
      qsymbol -> env -> (EcPath.path * EcTypes.ty option * idlookup_t) option
end

(* -------------------------------------------------------------------- *)
type ebinding = [
  | `Variable  of bool * EcTypes.ty
  | `Function  of funsig
  | `Module    of tymod
  | `ModType   of tymod
]

val bind1   : EcIdent.t * ebinding -> env -> env
val bindall : (EcIdent.t * ebinding) list -> env -> env
