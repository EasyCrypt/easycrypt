(* -------------------------------------------------------------------- *)
open EcUtils
open EcPath
open EcSymbols
open EcTypes
open EcMemory
open EcDecl
open EcFol
open EcModules
open EcTheory

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

val is_suspended : 'a suspension -> bool

(* -------------------------------------------------------------------- *)

(* Describe the kind of objects that can be bound in an environment.
 * We alse define 2 classes of objects:
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
  vb_kind  : EcTypes.pvar_kind;
}

type preenv = private {
  (* The current scope path, i.e. the path to the current active
   * theory/module. All paths of inserted objects are computed
   * from that value. *)
  env_scope  : EcPath.mpath;

  (* The sets of object living reachable from the current active
   * scope. This includes objects imported via the [require import]
   * commands and defined in the currently active scope. *)
  env_current : activemc;

  (* The sets of `compoments' (see the documentation of the [premc])
   * for each container (theory/module) living in the environment.
   * This is the unique point where the fully resolved components of
   * a container is stored. *)
  env_comps  : premc EcPath.Mp.t;

  (* The set of local variables *)
  env_locals : (EcIdent.t * EcTypes.ty) MMsym.t;

  (* The set of memories (i.e. sided program variables) *)
  env_memories : actmem MMsym.t;

  (* The active memory *)
  env_actmem : EcMemory.memory option;
 
  (* Why3 environment && meta-data *)
  env_w3     : EcWhy3.env;
  env_rb     : EcWhy3.rebinding;        (* in reverse order *)
  env_item   : ctheory_item list        (* in reverse order *)
}

(* A [premc] value describes the components (i.e. resolved members)
 * of a container, i.e. its variables, functions, sub-theories, ...
 * We maintain an invariant that, for a given object kind, a name
 * cannot be bound twice.
 *
 * Sub-containers also contain an entry in the [mc_components] set.
 * This set only records the presence of a field with a container.
 * The contents (components) of the container must be looked up using
 * the [env_comps] field of the associated environment.
 *
 * The field [mc_parameters] records the (module) parameter of the
 * associated container (module).
 *)
and premc = private {
  mc_parameters : (EcIdent.t * module_type)        list;
  mc_variables  : (mpath * varbind)                Msym.t;
  mc_functions  : (mpath * EcModules.function_)    Msym.t;
  mc_modules    : (mpath * EcModules.module_expr)  Msym.t;
  mc_modtypes   : (mpath * EcModules.module_sig)   Msym.t;
  mc_typedecls  : (mpath * EcDecl.tydecl)          Msym.t;
  mc_operators  : (mpath * EcDecl.operator)        Msym.t;
  mc_axioms     : (mpath * EcDecl.axiom)           Msym.t;
  mc_theories   : (mpath * ctheory)                Msym.t;
  mc_components : path                             Msym.t;
}

(* As [premc], but allows names to be bound several times, and maps
 * objects to [epath] instead of [path]. This structure serves as the
 * components description of the current active scope. It includes all
 * the objects imported via the [import] command. *)

and activemc = {
  amc_variables  : (mpath * varbind)                MMsym.t;
  amc_functions  : (mpath * EcModules.function_)    MMsym.t;
  amc_modules    : (mpath * EcModules.module_expr)  MMsym.t;
  amc_modtypes   : (mpath * EcModules.module_sig)   MMsym.t;
  amc_typedecls  : (mpath * EcDecl.tydecl)          MMsym.t;
  amc_operators  : (mpath * EcDecl.operator)        MMsym.t;
  amc_axioms     : (mpath * EcDecl.axiom)           MMsym.t;
  amc_theories   : (mpath * ctheory)                MMsym.t;
  amc_components : path                             MMsym.t;
}

and actmem =
| AMAbstract of EcIdent.t
| AMConcrete of mpath * memenv

(* -------------------------------------------------------------------- *)
type env = preenv

val preenv  : env -> preenv
val root    : env -> EcPath.path
val initial : env

(* -------------------------------------------------------------------- *)
val dump : ?name:string -> EcDebug.ppdebug -> env -> unit

(* -------------------------------------------------------------------- *)
exception LookupFailure of [`Path of path | `QSymbol of qsymbol]

(* -------------------------------------------------------------------- *)
type meerror =
| UnknownMemory of [`Symbol of symbol | `Memory of memory]

exception MEError of meerror

module Memory : sig
  val actmem_name : actmem -> EcIdent.t

  val set_active  : memory -> env -> env
  val get_active  : env -> memory option

  val byid     : memory -> env -> actmem option
  val lookup   : symbol -> env -> actmem option
  val current  : env -> (memory * actmem) option
  val push     : actmem -> env -> env
  val push_all : (mpath * memenv) list -> env -> env

  val concretize : mpath -> memenv -> env -> env
end

(* -------------------------------------------------------------------- *)
module Fun : sig
  type t = function_

  val by_path     : EcPath.path -> env -> t suspension
  val by_path_opt : EcPath.path -> env -> (t suspension) option
  val by_mpath    : EcPath.mpath -> env -> t
  val by_mpath_opt: EcPath.mpath -> env -> t option
  val lookup      : qsymbol -> env -> mpath * t
  val lookup_opt  : qsymbol -> env -> (mpath * t) option
  val lookup_path : qsymbol -> env -> mpath

  val sp_lookup     : qsymbol -> env -> (path * t suspension)
  val sp_lookup_opt : qsymbol -> env -> (path * t suspension) option

  val memenv     : hasres:bool -> memory -> EcPath.path -> env -> memenv
  val memenv_opt : hasres:bool -> memory -> EcPath.path -> env -> memenv option

  val enter : hasres:bool -> memory -> EcPath.mpath -> env -> (memenv * env)

  val add : EcPath.mpath -> env -> env
end

(* -------------------------------------------------------------------- *)
module Var : sig
  type t = varbind

  val by_path     : EcPath.path -> env -> t suspension
  val by_path_opt : EcPath.path -> env -> (t suspension) option
  val by_mpath    : EcPath.mpath -> env -> t
  val by_mpath_opt: EcPath.mpath -> env -> t option

  (* Lookup restricted to given kind of variables *)
  val lookup_locals    : symbol -> env -> (EcIdent.t * EcTypes.ty) list
  val lookup_local     : symbol -> env -> (EcIdent.t * EcTypes.ty)
  val lookup_local_opt : symbol -> env -> (EcIdent.t * EcTypes.ty) option

  val lookup_progvar     : ?side:memory -> qsymbol -> env -> (prog_var * EcTypes.ty)
  val lookup_progvar_opt : ?side:memory -> qsymbol -> env -> (prog_var * EcTypes.ty) option

  (* Locals binding *)
  val bind_local  : EcIdent.t -> EcTypes.ty -> env -> env
  val bind_locals : (EcIdent.t * EcTypes.ty) list -> env -> env

  (* Program variables binding *)
  val bind    : symbol -> pvar_kind -> EcTypes.ty -> env -> env
  val bindall : (symbol * EcTypes.ty) list -> pvar_kind -> env -> env

  val add : EcPath.mpath -> env -> env
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
  type t = module_expr

  val by_path     : EcPath.path -> env -> t suspension
  val by_path_opt : EcPath.path -> env -> (t suspension) option
  val by_mpath    : EcPath.mpath -> env -> t
  val by_mpath_opt: EcPath.mpath -> env -> t option
  val lookup      : qsymbol -> env -> mpath * t
  val lookup_opt  : qsymbol -> env -> (mpath * t) option
  val lookup_path : qsymbol -> env -> mpath

  val sp_lookup     : qsymbol -> env -> mpath * t suspension
  val sp_lookup_opt : qsymbol -> env -> (mpath * t suspension) option

  val add  : EcPath.mpath -> env -> env
  val bind : symbol -> module_expr -> env -> env

  val enter : symbol -> (EcIdent.t * module_type) list -> env -> env
  val bind_local : EcIdent.t -> module_type -> env -> env

  val unfold_mod_path : env -> EcPath.mpath -> EcPath.mpath
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

  val mod_type_equiv : env -> module_type -> module_type -> bool
  val has_mod_type : env -> module_type list -> module_type -> bool
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

  val add : EcPath.path -> env -> env

  val bind  : symbol -> ctheory_w3 -> env -> env
  val bindx : symbol -> ctheory -> env -> env

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
  | `Function  of function_
  | `Module    of module_expr
  | `ModType   of module_sig
]

val bind1   : symbol * ebinding -> env -> env
val bindall : (symbol * ebinding) list -> env -> env

val import_w3_dir :
     env -> string list -> string
  -> EcWhy3.renaming_decl
  -> env * ctheory_item list

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

val norm_pvar         : env -> prog_var -> prog_var
