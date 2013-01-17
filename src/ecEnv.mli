(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcDecl
open EcTypesmod

(* -------------------------------------------------------------------- *)
type varbind = {
  vb_type  : EcTypes.ty;
  vb_kind  : EcTypes.pvar_kind option;
}

type preenv = private {
  env_scope  : EcPath.path;
  env_root   : premc;
  env_comps  : (EcPath.path * premc) EcIdent.Mid.t;
  env_w3     : EcWhy3.env;
  env_rb     : EcWhy3.rebinding;        (* in reverse order *)
  env_item   : ctheory_item list        (* in reverse order *)
}

and premc = private {
  mc_variables  : (EcPath.path * varbind)            EcIdent.Map.t;
  mc_functions  : (EcPath.path * EcTypesmod.funsig)  EcIdent.Map.t;
  mc_modules    : (EcPath.path * EcTypesmod.tymod)   EcIdent.Map.t;
  mc_modtypes   : (EcPath.path * EcTypesmod.tymod)   EcIdent.Map.t;
  mc_typedecls  : (EcPath.path * EcDecl.tydecl)      EcIdent.Map.t;
  mc_operators  : (EcPath.path * EcDecl.operator)    EcIdent.Map.t;
  mc_axioms     : (EcPath.path * EcDecl.axiom)       EcIdent.Map.t;
  mc_theories   : (EcPath.path * EcTypesmod.ctheory) EcIdent.Map.t;
  mc_components : unit EcIdent.Map.t;
}

(* -------------------------------------------------------------------- *)
type env = preenv

val preenv  : env -> preenv
val initial : env
val root    : env -> EcPath.path

(* -------------------------------------------------------------------- *)
val dump : ?name:string -> EcDebug.ppdebug -> env -> unit

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

module Ax    : sig 
  include S with type t = axiom
  val instanciate : EcPath.path -> EcTypes.ty list -> env -> EcFol.form
end

module ModTy : S with type t = tymod

(* -------------------------------------------------------------------- *)
module Var : sig
  type t = varbind

  val lookup_by_path    : EcPath.path -> env -> t        (* full path *)
  val trylookup_by_path : EcPath.path -> env -> t option (* full path *)
  val lookup            : qsymbol -> env -> EcPath.path * t
  val trylookup         : qsymbol -> env -> (EcPath.path * t) option
  val exists            : qsymbol -> env -> bool

  val bind :
       EcIdent.t
    -> EcTypes.ty
    -> EcTypes.pvar_kind option
    -> env
    -> env

  val bindall :
       (EcIdent.t * EcTypes.ty) list
    -> EcTypes.pvar_kind option
    -> env
    -> env
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
type ctheory_w3

val ctheory_of_ctheory_w3 : ctheory_w3 -> ctheory

module Theory : sig
  type t = ctheory_w3

  val bind : EcIdent.t -> t -> env -> env
  val bindall : (EcIdent.t * t) list -> env -> env
  val lookup_by_path : EcPath.path -> env -> ctheory
  val lookup : EcSymbols.qsymbol -> env -> EcPath.path * ctheory
  val trylookup_by_path : EcPath.path -> env -> ctheory option
  val trylookup : EcSymbols.qsymbol -> env -> (EcPath.path * ctheory) option
  val exists : EcSymbols.qsymbol -> env -> bool
  val import : EcPath.path -> env -> env
  val export : EcPath.path -> env -> env
  val require : EcIdent.t -> ctheory_w3 -> env -> env
  val enter : EcSymbols.symbol -> env -> EcIdent.t * env
  val close : env -> ctheory_w3
end

(* -------------------------------------------------------------------- *)
module Op : sig
  include S with type t = operator

  val all : (operator -> bool) -> qsymbol -> env -> (EcPath.path * t) list
end

(* -------------------------------------------------------------------- *)
module Ty : sig
  include S with type t = tydecl

  val defined : EcPath.path -> env -> bool
  val unfold  : EcPath.path -> EcTypes.ty list -> env -> EcTypes.ty
end

(* -------------------------------------------------------------------- *)

module Ident : sig
  type idlookup_t = 
    [ `Local of EcIdent.t
    | `Pvar of EcTypes.prog_var 
    | `Ctnt of EcPath.path * operator ]

  val lookup    : 
      (operator -> bool) -> qsymbol -> env -> (EcTypes.ty * idlookup_t) 

  val trylookup : 
      (operator -> bool) -> qsymbol -> env -> (EcTypes.ty * idlookup_t) list

end

(* -------------------------------------------------------------------- *)
type ebinding = [
  | `Variable  of EcTypes.pvar_kind option * EcTypes.ty
  | `Function  of funsig
  | `Module    of tymod
  | `ModType   of tymod
]

val bind1   : EcIdent.t * ebinding -> env -> env
val bindall : (EcIdent.t * ebinding) list -> env -> env

val import_w3_dir :
     env -> string list -> string
  -> EcWhy3.renaming_decl
  -> env * EcTypesmod.ctheory_item list

(* -------------------------------------------------------------------- *)

val equal_type        : env -> EcTypes.ty -> EcTypes.ty -> bool
val check_type        : env -> EcTypes.ty -> EcTypes.ty -> unit
val check_alpha_equal : env -> EcFol.form -> EcFol.form -> unit
val is_alpha_equal    : env -> EcFol.form -> EcFol.form -> bool

val check_goal        : env -> EcFol.l_decl -> bool


