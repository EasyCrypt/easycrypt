(* -------------------------------------------------------------------- *)
open EcUtils
open EcPath
open EcSymbols
open EcTypes
open EcDecl
open EcFol
open EcTypesmod

(* -------------------------------------------------------------------- *)

(* A [path] is missing the module application information. As such, when
 * resolving a path, it is not returned a object but a suspension to
 * that object. This suspension can resolved by providing the missing
 * modules parameters. Such a resolved suspension only contains path of the
 * for [EPath _]. See the environment API for more information.
 *)
type 'a suspension = {
  sp_target : 'a;
  sp_params : (EcIdent.t * module_type) list list;
}

(* -------------------------------------------------------------------- *)

(* Describe the kind of objects that can be bound in an environment.
 * We alse define define 2 classes of objects:
 * - containers    : theory   / module
 * - module values : variable / function
 *)

type okind = [
  | `Variable
  | `Function
  | `Theory
  | `Module
  | `ModType
  | `TypeDecls
  | `OpDecls
  | `Lemma
]

module Kinds : EcUtils.IFlags with type flag = okind

val ok_container : Kinds.t
val ok_modvalue  : Kinds.t

(* -------------------------------------------------------------------- *)
type varbind = {
  vb_type  : EcTypes.ty;
  vb_kind  : EcTypes.pvar_kind option;
}

type preenv = private {
  (* The current scope path, i.e. the path to the current active
   * theory/module. All paths of inserted objects are computed
   * from that value. *)
  env_scope  : EcPath.path;

  (* The sets of object living reachable from the current active
   * scope. This includes objects imported via the [require import]
   * commands and defined in the currently active scope. *)
  env_current : activemc;

  (* The sets of `compoments' (see the documentation of the [premc])
   * for each container (theory/module) living in the environment.
   * This is the unique point where the fully resolved components of
   * a container is stored. We store components of bound module
   * parameters in a different map than top-level ones. *)
  env_comps  : premc EcPath.Mp.t;
  env_bcomps : premc EcIdent.Mid.t;

  env_w3     : EcWhy3.env;
  env_rb     : EcWhy3.rebinding;        (* in reverse order *)
  env_item   : ctheory_item list        (* in reverse order *)
}

(* A [premc] value described the components (i.e. resolved members)
 * of a container, i.e. its variables, functions, sub-theories, ...
 * We maintain an invariant that, for a given object kind, a name
 * cannot be bound twice.
 *
 * Sub-containers also contain an entry in the [mc_components] set.
 * This set only records the presence of a field with a container.
 * The contents (compoments) of the container must be looked up using
 * the [env_comps] field of the associated environment.
 *
 * The field [mc_parameters] records the (module) parameter of the
 * associated container (module).
 *)
and premc = private {
  mc_parameters : (EcIdent.t * module_type)       list;
  mc_variables  : (path * varbind)                Msym.t;
  mc_functions  : (path * EcTypesmod.funsig)      Msym.t;
  mc_modules    : (path * EcTypesmod.module_expr) Msym.t;
  mc_modtypes   : (path * EcTypesmod.module_sig)  Msym.t;
  mc_typedecls  : (path * EcDecl.tydecl)          Msym.t;
  mc_operators  : (path * EcDecl.operator)        Msym.t;
  mc_axioms     : (path * EcDecl.axiom)           Msym.t;
  mc_theories   : (path * EcTypesmod.ctheory)     Msym.t;
  mc_components : path                            Msym.t;
}

(* As for [premc], but allows names to be bound several time, and maps
 * objects to [epath] instead of [path]. This structure serves as the
 * components description of the current active scope. It includes all
 * the objects imported via the [import] command. *)

and activemc = {
  amc_variables  : (epath * varbind)                MMsym.t;
  amc_functions  : (epath * EcTypesmod.funsig)      MMsym.t;
  amc_modules    : ( cref * EcTypesmod.module_expr) MMsym.t;
  amc_modtypes   : ( path * EcTypesmod.module_sig)  MMsym.t;
  amc_typedecls  : ( path * EcDecl.tydecl)          MMsym.t;
  amc_operators  : ( path * EcDecl.operator)        MMsym.t;
  amc_axioms     : ( path * EcDecl.axiom)           MMsym.t;
  amc_theories   : ( path * EcTypesmod.ctheory)     MMsym.t;
  amc_components : cref                             MMsym.t;
}

(* -------------------------------------------------------------------- *)
type env = preenv

val preenv  : env -> preenv
val root    : env -> EcPath.path
val initial : env

(* -------------------------------------------------------------------- *)
val dump : ?name:string -> EcDebug.ppdebug -> env -> unit

(* -------------------------------------------------------------------- *)
exception LookupFailure of [`Path of epath | `QSymbol of qsymbol]

(* -------------------------------------------------------------------- *)
module Fun : sig
  type t = funsig suspension

  val by_path     : EcPath.path -> env -> t
  val by_path_opt : EcPath.path -> env -> t option
  val lookup      : qsymbol -> env -> epath * t
  val lookup_opt  : qsymbol -> env -> (epath * t) option
  val lookup_path : qsymbol -> env -> epath

  val add : EcPath.path -> env -> env
end

(* -------------------------------------------------------------------- *)
module Var : sig
  type t = varbind

  val by_path     : EcPath.path -> env -> t
  val by_path_opt : EcPath.path -> env -> t option
  val lookup      : qsymbol -> env -> cref * t
  val lookup_opt  : qsymbol -> env -> (cref * t) option
  val lookup_path : qsymbol -> env -> cref

  (* Lookup restricted to given kind of variables *)
  val lookup_locals    : symbol -> env -> (EcIdent.t * EcTypes.ty) list
  val lookup_local     : symbol -> env -> (EcIdent.t * EcTypes.ty)
  val lookup_local_opt : symbol -> env -> (EcIdent.t * EcTypes.ty) option

  val lookup_progvars    : qsymbol -> env -> (prog_var * EcTypes.ty) list
  val lookup_progvar     : qsymbol -> env -> (prog_var * EcTypes.ty)
  val lookup_progvar_opt : qsymbol -> env -> (prog_var * EcTypes.ty) option

  (* Locals binding *)
  val bind_local  : EcIdent.t -> EcTypes.ty -> env -> env
  val bind_locals : (EcIdent.t * EcTypes.ty) list -> env -> env

  (* Program variables binding *)
  val bind    : symbol -> pvar_kind -> EcTypes.ty -> env -> env
  val bindall : (symbol * EcTypes.ty) list -> pvar_kind -> env -> env

  val add : EcPath.path -> env -> env
end

(* -------------------------------------------------------------------- *)
module Ax : sig
  type t = axiom

  val by_path     : EcPath.path -> env -> t
  val by_path_opt : EcPath.path -> env -> t option
  val lookup      : qsymbol -> env -> EcPath.path * t
  val lookup_opt  : qsymbol -> env -> (EcPath.path * t) option
  val lookup_path : qsymbol -> env -> EcPath.path

  val add  : EcPath.path -> env -> env
  val bind : symbol -> axiom -> env -> env

  val instanciate : EcPath.path -> EcTypes.ty list -> env -> EcFol.form
end

(* -------------------------------------------------------------------- *)
module Mod : sig
  type t = module_expr suspension

  val by_path     : EcPath.path -> env -> t
  val by_path_opt : EcPath.path -> env -> t option
  val lookup      : qsymbol -> env -> cref * t
  val lookup_opt  : qsymbol -> env -> (cref * t) option
  val lookup_path : qsymbol -> env -> cref

  (* Locals binding *)
  val bind_local  : EcIdent.t -> module_expr -> env -> env
  val bind_locals : (EcIdent.t * module_expr) list -> env -> env

  val add  : EcPath.path -> env -> env
  val bind : symbol -> module_expr -> env -> env
end

(* -------------------------------------------------------------------- *)
module ModTy : sig
  type t = module_sig

  val by_path     : EcPath.path -> env -> t
  val by_path_opt : EcPath.path -> env -> t option
  val lookup      : qsymbol -> env -> EcPath.path * t
  val lookup_opt  : qsymbol -> env -> (EcPath.path * t) option
  val lookup_path : qsymbol -> env -> EcPath.path

  val add  : EcPath.path -> env -> env
  val bind : symbol -> t -> env -> env
end

(* -------------------------------------------------------------------- *)
type ctheory_w3

val ctheory_of_ctheory_w3 : ctheory_w3 -> ctheory

module Theory : sig
  type t = ctheory

  val by_path     : EcPath.path -> env -> t
  val by_path_opt : EcPath.path -> env -> t option
  val lookup      : qsymbol -> env -> EcPath.path * t
  val lookup_opt  : qsymbol -> env -> (EcPath.path * t) option
  val lookup_path : qsymbol -> env -> EcPath.path

  val add  : EcPath.path -> env -> env
  val bind : symbol -> ctheory_w3 -> env -> env

  val require : symbol -> ctheory_w3 -> env -> env
  val import  : EcPath.path -> env -> env
  val export  : EcPath.path -> env -> env

  val enter : symbol -> env -> env
  val close : env -> ctheory_w3
end

(* -------------------------------------------------------------------- *)
module Op : sig
  type t = operator

  val by_path     : EcPath.path -> env -> t
  val by_path_opt : EcPath.path -> env -> t option
  val lookup      : qsymbol -> env -> EcPath.path * t
  val lookup_opt  : qsymbol -> env -> (EcPath.path * t) option
  val lookup_path : qsymbol -> env -> EcPath.path

  val add  : EcPath.path -> env -> env
  val bind : symbol -> operator -> env -> env

  val all : (operator -> bool) -> qsymbol -> env -> (EcPath.path * t) list
end

(* -------------------------------------------------------------------- *)
module Ty : sig
  type t = EcDecl.tydecl

  val by_path     : EcPath.path -> env -> t
  val by_path_opt : EcPath.path -> env -> t option
  val lookup      : qsymbol -> env -> EcPath.path * t
  val lookup_opt  : qsymbol -> env -> (EcPath.path * t) option
  val lookup_path : qsymbol -> env -> EcPath.path

  val add  : EcPath.path -> env -> env
  val bind : symbol -> t -> env -> env

  val defined : EcPath.path -> env -> bool
  val unfold  : EcPath.path -> EcTypes.ty list -> env -> EcTypes.ty
end

(* -------------------------------------------------------------------- *)
type ebinding = [
  | `Variable  of EcTypes.pvar_kind * EcTypes.ty
  | `Function  of funsig
  | `Module    of module_expr
  | `ModType   of module_sig
]

val bind1   : symbol * ebinding -> env -> env
val bindall : (symbol * ebinding) list -> env -> env

val import_w3_dir :
     env -> string list -> string
  -> EcWhy3.renaming_decl
  -> env * EcTypesmod.ctheory_item list

(* -------------------------------------------------------------------- *)
exception IncompatibleType of EcTypes.ty * EcTypes.ty
exception IncompatibleForm of form * form * form * form

val equal_type        : env -> EcTypes.ty -> EcTypes.ty -> bool
val check_type        : env -> EcTypes.ty -> EcTypes.ty -> unit
val destr_tfun        : env -> EcTypes.ty -> EcTypes.ty * EcTypes.ty
val ty_fun_app        : env -> EcTypes.ty -> EcTypes.ty list -> EcTypes.ty
val check_alpha_equal : env -> EcFol.form -> EcFol.form -> unit
val is_alpha_equal    : env -> EcFol.form -> EcFol.form -> bool
val check_goal        : env -> EcWhy3.prover_infos -> EcFol.l_decl -> bool
