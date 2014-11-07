(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2014 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcPath
open EcSymbols
open EcTypes
open EcMemory
open EcDecl
open EcCoreFol
open EcModules
open EcTheory
open EcProvers

(* -------------------------------------------------------------------- *)
type 'a suspension = {
  sp_target : 'a;
  sp_params : int * (EcIdent.t * module_type) list;
}

(* -------------------------------------------------------------------- *)
type varbind = {
  vb_type  : EcTypes.ty;
  vb_kind  :  [ `Proj of int | `Var of EcTypes.pvar_kind ];
}

(* -------------------------------------------------------------------- *)
type env

val initial : EcGState.gstate -> env
val root    : env -> EcPath.path
val mroot   : env -> EcPath.mpath
val xroot   : env -> EcPath.xpath option

(* -------------------------------------------------------------------- *)
val gstate : env -> EcGState.gstate

(* -------------------------------------------------------------------- *)
val notify : env -> EcGState.loglevel -> ('a, unit, string, unit) format4 -> 'a

(* -------------------------------------------------------------------- *)
type lookup_error = [
  | `XPath   of xpath
  | `MPath   of mpath
  | `Path    of path
  | `QSymbol of qsymbol
  | `AbsStmt of EcIdent.t
]

exception LookupFailure of lookup_error

(* -------------------------------------------------------------------- *)
type meerror =
| UnknownMemory of [`Symbol of symbol | `Memory of memory]

exception MEError of meerror

module Memory : sig
  val all         : env -> memenv list
  val set_active  : memory -> env -> env
  val get_active  : env -> memory option

  val byid        : memory -> env -> memenv option
  val lookup      : int -> symbol -> env -> memenv option
  val current     : env -> memenv option
  val push        : memenv -> env -> env
  val push_all    : memenv list -> env -> env
  val push_active : memenv -> env -> env
end

(* -------------------------------------------------------------------- *)
module Fun : sig
  type t = function_

  val by_xpath    : xpath -> env -> t
  val by_xpath_opt: xpath -> env -> t option
  val lookup      : qsymbol -> env -> xpath * t
  val lookup_opt  : qsymbol -> env -> (xpath * t) option
  val lookup_path : qsymbol -> env -> xpath

  val sp_lookup      : qsymbol -> env -> xpath * t suspension
  val sp_lookup_opt  : qsymbol -> env -> (xpath * t suspension) option

  val enter : symbol -> env -> env
  val add   : xpath -> env -> env

  (* ------------------------------------------------------------------ *)
  (* FIXME: what are these functions for? *)
  val prF_memenv : EcMemory.memory -> xpath -> env -> memenv

  val prF : xpath -> env -> env

  val hoareF_memenv : xpath -> env -> memenv * memenv

  val hoareF : xpath -> env -> env * env

  val hoareS : xpath -> env -> memenv * (funsig * function_def) * env

  val actmem_post :  memory -> xpath -> function_ -> memenv

  val inv_memenv : env -> env

  val equivF_memenv : xpath -> xpath -> env ->
    (memenv * memenv) * (memenv * memenv)

  val equivF : xpath -> xpath -> env -> env * env

  val equivS : xpath -> xpath -> env ->
    memenv * (funsig * function_def) * memenv * (funsig * function_def) * env
end

(* -------------------------------------------------------------------- *)
module Var : sig
  type t = varbind

  val by_xpath     : xpath -> env -> t
  val by_xpath_opt : xpath -> env -> t option

  (* Lookup restricted to given kind of variables *)
  val lookup_locals    : symbol -> env -> (EcIdent.t * EcTypes.ty) list
  val lookup_local     : symbol -> env -> (EcIdent.t * EcTypes.ty)
  val lookup_local_opt : symbol -> env -> (EcIdent.t * EcTypes.ty) option

  val lookup_progvar     : ?side:memory -> qsymbol -> env ->
    ([`Proj of EcTypes.prog_var * EcTypes.ty * (int*int) | `Var of EcTypes.prog_var ] *
     EcTypes.ty)
  val lookup_progvar_opt : ?side:memory -> qsymbol -> env ->
    ([`Proj of EcTypes.prog_var * EcTypes.ty * (int*int) | `Var of EcTypes.prog_var ] *
     EcTypes.ty) option

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

  val instanciate : path -> EcTypes.ty list -> env -> form
end

(* -------------------------------------------------------------------- *)
module Mod : sig
  type t = module_expr

  val by_mpath    : mpath -> env -> t
  val by_mpath_opt: mpath -> env -> t option
  val lookup      : qsymbol -> env -> mpath * t
  val lookup_opt  : qsymbol -> env -> (mpath * t) option
  val lookup_path : qsymbol -> env -> mpath

  val sp_lookup     : qsymbol -> env -> mpath * (module_expr suspension)
  val sp_lookup_opt : qsymbol -> env -> (mpath * (module_expr suspension)) option

  val bind : symbol -> module_expr -> env -> env

  val enter : symbol -> (EcIdent.t * module_type) list -> env -> env
  val bind_local : EcIdent.t -> module_type -> mod_restr -> env -> env

  val declare_local : EcIdent.t -> module_type -> mod_restr -> env -> env

  val add_restr_to_locals : mod_restr -> env -> env

  (* Only bind module, ie no memory and no local variable *)
  val add_mod_binding : binding -> env -> env

  val add : mpath -> env -> env
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
  val sig_of_mt :  env -> module_type -> module_sig
end

(* -------------------------------------------------------------------- *)
type use = {
  us_pv : ty EcPath.Mx.t;
  us_gl : EcIdent.Sid.t;
}

module NormMp : sig
  val norm_mpath : env -> mpath -> mpath
  val norm_xfun  : env -> xpath -> xpath
  val norm_pvar  : env -> EcTypes.prog_var -> EcTypes.prog_var
  val norm_form  : env -> form -> form
  val mod_use    : env -> mpath -> use
  val fun_use    : env -> xpath -> use
  val norm_restr : env -> mod_restr  -> use
  val equal_restr : env -> mod_restr -> mod_restr -> bool
  val get_restr  : env -> mpath -> use
  val use_mem_xp : xpath -> use -> bool
  val use_mem_gl : mpath -> use -> bool
  val norm_glob  : env -> EcMemory.memory -> mpath -> form
  val norm_tglob : env -> mpath -> EcTypes.ty
  val tglob_reducible : env -> mpath -> bool
  val is_abstract_fun : xpath -> env -> bool
  val x_equal        : env -> xpath -> xpath -> bool
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

  val is_projection  : env -> path -> bool
  val is_record_ctor : env -> path -> bool
  val is_dtype_ctor  : env -> path -> bool
  val is_fix_def     : env -> path -> bool
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
  val hnorm   : EcTypes.ty -> env -> EcTypes.ty

  val scheme_of_ty :
    [`Ind | `Case] -> EcTypes.ty -> env -> (path * EcTypes.ty list) option
end

(* -------------------------------------------------------------------- *)
module Algebra : sig
  val add_ring  : ty -> EcDecl.ring  -> env -> env
  val add_field : ty -> EcDecl.field -> env -> env
end

(* -------------------------------------------------------------------- *)
module TypeClass : sig
  type t = typeclass

  val add   : path -> env -> env
  val bind  : symbol -> t -> env -> env
  val graph : env -> EcTypeClass.graph

  val by_path     : path -> env -> t
  val by_path_opt : path -> env -> t option
  val lookup      : qsymbol -> env -> path * t
  val lookup_opt  : qsymbol -> env -> (path * t) option
  val lookup_path : qsymbol -> env -> path

  val add_instance  : (ty_params * ty) -> tcinstance -> env -> env
  val get_instances : env -> ((ty_params * ty) * tcinstance) list
end
(* -------------------------------------------------------------------- *)
module BaseRw : sig
  type t = Sp.t
  val by_path : path -> env -> Sp.t 
  val lookup : qsymbol -> env -> path * Sp.t
  val lookup_opt : qsymbol -> env -> (path * Sp.t) option
  val is_base : qsymbol -> env -> bool
  val bind : symbol -> env -> env
  val bind_addrw : path -> path list -> env -> env
end
(* -------------------------------------------------------------------- *)
module AbsStmt : sig
  type t = EcBaseLogic.abs_uses

  val byid : EcIdent.t -> env -> t
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
open EcBaseLogic

module LDecl : sig
  type error =
    | UnknownSymbol   of EcSymbols.symbol
    | UnknownIdent    of EcIdent.t
    | NotAVariable    of EcIdent.t
    | NotAHypothesis  of EcIdent.t
    | CanNotClear     of EcIdent.t * EcIdent.t
    | DuplicateIdent  of EcIdent.t
    | DuplicateSymbol of EcSymbols.symbol

  exception Ldecl_error of error

  type hyps

  val init    : env -> ?locals:EcBaseLogic.l_local list -> ty_params -> hyps
  val tohyps  : hyps -> EcBaseLogic.hyps
  val toenv   : hyps -> env
  val baseenv : hyps -> env

  val add_local : EcIdent.t -> local_kind -> hyps -> hyps

  val lookup : symbol -> hyps -> l_local

  val reducible_var : EcIdent.t -> hyps -> bool
  val reduce_var    : EcIdent.t -> hyps -> form
  val lookup_var    : symbol -> hyps -> EcIdent.t * ty

  val lookup_by_id     : EcIdent.t -> hyps -> local_kind
  val lookup_hyp_by_id : EcIdent.t -> hyps -> form

  val has_hyp : symbol -> hyps -> bool
  val lookup_hyp : symbol -> hyps -> EcIdent.t * form
  val get_hyp : EcIdent.t * local_kind -> EcIdent.t * form

  val has_symbol : symbol -> hyps -> bool

  val fresh_id  : hyps -> symbol -> EcIdent.t
  val fresh_ids : hyps -> symbol list -> EcIdent.t list

  val clear : EcIdent.Sid.t -> hyps -> hyps

  val ld_subst : f_subst -> local_kind -> local_kind

  val push_all    : memenv list -> hyps -> hyps
  val push_active : memenv -> hyps -> hyps

  val hoareF : xpath -> hyps -> hyps * hyps
  val equivF : xpath -> xpath -> hyps -> hyps * hyps
  val inv_memenv  : hyps -> hyps
  val inv_memenv1 : hyps -> hyps
end

(* -------------------------------------------------------------------- *)
val check_goal : bool * hints -> EcProvers.prover_infos -> LDecl.hyps * form -> bool
