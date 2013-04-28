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
  sp_params : (EcIdent.t * module_type) list;
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


(* -------------------------------------------------------------------- *)
type env 

val root    : env -> path
val mroot   : env -> xpath
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

  val set_active  : memory -> env -> env
  val get_active  : env -> memory option

  val byid        : memory -> env -> memenv option
  val lookup      : symbol -> env -> memenv option
  val current     : env -> memenv option
  val push        : memenv -> env -> env
  val push_all    : memenv list -> env -> env
  val push_active : memenv -> env -> env

end

(* -------------------------------------------------------------------- *)
module Fun : sig
  type t = function_

  val by_path     : mpath_top -> path -> env -> t suspension
  val by_path_opt : mpath_top -> path -> env -> (t suspension) option
  val by_xpath    : xpath -> env -> t
  val by_xpath_opt: xpath -> env -> t option
  val lookup      : qsymbol -> env -> xpath * t
  val lookup_opt  : qsymbol -> env -> (xpath * t) option
  val lookup_path : qsymbol -> env -> xpath

  val sp_lookup     : qsymbol -> env -> (mpath_top * path * t suspension)
  val sp_lookup_opt : qsymbol -> env -> 
    (mpath_top * path * t suspension) option

  val prF : xpath -> env -> env

  val hoareF_memenv : xpath -> env -> memenv * memenv

  val hoareF : xpath -> env -> env * env

  val hoareS : xpath -> env -> memenv * function_def * env

  val hoareS_anonym : variable list -> env -> memenv * env

  val actmem_post :  memory -> xpath -> function_ -> memenv

  val equivF_memenv : xpath -> xpath -> env -> 
    (memenv * memenv) * (memenv * memenv) 

  val equivF : xpath -> xpath -> env -> env * env

  val equivS : xpath -> xpath -> env -> 
    memenv * function_def * memenv * function_def * env

  val equivS_anonym : variable list -> variable list -> env -> 
    memenv * memenv * env

  val enter : symbol -> env -> env
  val add : xpath -> env -> env
end

(* -------------------------------------------------------------------- *)
module Var : sig
  type t = varbind

  val by_path     : xpath -> env -> t
  val by_path_opt : xpath -> env -> t option

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

  val add : xpath -> env -> env
end

(* -------------------------------------------------------------------- *)
module Ax : sig
  type t = axiom

  val by_path     : path -> env -> t
  val by_path_opt : path -> env -> t option
  val lookup      : qsymbol -> env -> path * t
  val lookup_opt  : qsymbol -> env -> (path * t) option
  val lookup_path : qsymbol -> env -> path

  val add  : path -> env -> env
  val bind : symbol -> axiom -> env -> env

  val instanciate : path -> EcTypes.ty list -> env -> EcFol.form
end

(* -------------------------------------------------------------------- *)
module Mod : sig
  type t = module_expr

  val by_path     : mpath_top -> env -> t suspension
  val by_path_opt : mpath_top -> env -> (t suspension) option
  val by_mpath    : mpath -> env -> t
  val by_mpath_opt: mpath -> env -> t option
  val lookup      : qsymbol -> env -> mpath * t
  val lookup_opt  : qsymbol -> env -> (mpath * t) option
  val lookup_path : qsymbol -> env -> mpath

  val bind : symbol -> module_expr -> env -> env

  val enter : symbol -> (EcIdent.t * module_type) list -> env -> env
  val bind_local : EcIdent.t -> module_type -> env -> env

end

(* -------------------------------------------------------------------- *)
module ModTy : sig
  type t = module_sig

  val by_path     : path -> env -> t
  val by_path_opt : path -> env -> t option
  val lookup      : qsymbol -> env -> path * t
  val lookup_opt  : qsymbol -> env -> (path * t) option
  val lookup_path : qsymbol -> env -> path

  val add  : path -> env -> env
  val bind : symbol -> t -> env -> env

  val mod_type_equiv : env -> module_type -> module_type -> bool
  val has_mod_type : env -> module_type list -> module_type -> bool
end

(* -------------------------------------------------------------------- *)
module NormMp : sig
  val norm_mpath : env -> mpath -> mpath
  val norm_xpath : env -> xpath -> xpath
  val norm_pvar  : env -> EcTypes.prog_var -> EcTypes.prog_var
end

(* -------------------------------------------------------------------- *)
type ctheory_w3

val ctheory_of_ctheory_w3 : ctheory_w3 -> ctheory

module Theory : sig
  type t = ctheory

  val by_path     : path -> env -> t
  val by_path_opt : path -> env -> t option
  val lookup      : qsymbol -> env -> path * t
  val lookup_opt  : qsymbol -> env -> (path * t) option
  val lookup_path : qsymbol -> env -> path

  val add : path -> env -> env

  val bind  : symbol -> ctheory_w3 -> env -> env
  val bindx : symbol -> ctheory -> env -> env

  val require : symbol -> ctheory_w3 -> env -> env
  val import  : path -> env -> env
  val export  : path -> env -> env

  val enter : symbol -> env -> env
  val close : env -> ctheory_w3
end

(* -------------------------------------------------------------------- *)
module Op : sig
  type t = operator

  val by_path     : path -> env -> t
  val by_path_opt : path -> env -> t option
  val lookup      : qsymbol -> env -> path * t
  val lookup_opt  : qsymbol -> env -> (path * t) option
  val lookup_path : qsymbol -> env -> path

  val add  : path -> env -> env
  val bind : symbol -> operator -> env -> env

  val all : (operator -> bool) -> qsymbol -> env -> (path * t) list
  val reducible : env -> path -> bool
  val reduce    : env -> path -> ty list -> form
end

(* -------------------------------------------------------------------- *)
module Ty : sig
  type t = EcDecl.tydecl

  val by_path     : path -> env -> t
  val by_path_opt : path -> env -> t option
  val lookup      : qsymbol -> env -> path * t
  val lookup_opt  : qsymbol -> env -> (path * t) option
  val lookup_path : qsymbol -> env -> path

  val add  : path -> env -> env
  val bind : symbol -> t -> env -> env

  val defined : path -> env -> bool
  val unfold  : path -> EcTypes.ty list -> env -> EcTypes.ty
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
val check_goal : env -> EcProvers.prover_infos -> EcBaseLogic.l_decl -> bool
