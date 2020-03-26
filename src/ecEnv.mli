(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
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
val astop   : env -> env

(* -------------------------------------------------------------------- *)
val gstate : env -> EcGState.gstate
val copy   : env -> env

(* -------------------------------------------------------------------- *)
val notify :
     ?immediate:bool -> env -> EcGState.loglevel
  -> ('a, Format.formatter, unit, unit) format4 -> 'a

(* -------------------------------------------------------------------- *)
type lookup_error = [
  | `XPath   of xpath
  | `MPath   of mpath
  | `Path    of path
  | `QSymbol of qsymbol
  | `AbsStmt of EcIdent.t
]

exception LookupFailure of lookup_error
exception DuplicatedBinding of symbol

(* -------------------------------------------------------------------- *)
exception NotReducible

(* -------------------------------------------------------------------- *)
type meerror =
| UnknownMemory of [`Symbol of symbol | `Memory of memory]

exception MEError of meerror

module Memory : sig
  val all         : env -> memenv list
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

  val inv_memory : [`Left|`Right] -> env -> memenv

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

  val iter : ?name:qsymbol -> (path -> axiom -> unit) -> env -> unit

  val all :
    ?check:(path -> axiom -> bool) -> ?name:qsymbol -> env -> (path * t) list

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
  val add_mod_binding : bindings -> env -> env

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
  val x_equal         : env -> xpath -> xpath -> bool
  val pv_equal        : env -> EcTypes.prog_var -> EcTypes.prog_var -> bool
end

(* -------------------------------------------------------------------- *)
module Theory : sig
  type t    = ctheory
  type mode = [`All | thmode]

  val by_path     : ?mode:mode -> path -> env -> (t * thmode)
  val by_path_opt : ?mode:mode -> path -> env -> (t * thmode) option
  val lookup      : ?mode:mode -> qsymbol -> env -> path * (t * thmode)
  val lookup_opt  : ?mode:mode -> qsymbol -> env -> (path * (t * thmode)) option
  val lookup_path : ?mode:mode -> qsymbol -> env -> path

  val add  : path -> env -> env
  val bind : ?mode:thmode -> symbol -> ctheory -> env -> env

  val require : ?mode:thmode -> symbol -> ctheory -> env -> env
  val import  : path -> env -> env
  val export  : path -> env -> env

  val enter : symbol -> env -> env

  val close :
       ?clears:(path list)
    -> ?pempty:[`Full | `ClearOnly | `No]
    -> env -> ctheory option
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

  val all : ?check:(operator -> bool) -> qsymbol -> env -> (path * t) list

  val reducible : env -> path -> bool
  val reduce    : env -> path -> ty list -> form

  val is_projection  : env -> path -> bool
  val is_record_ctor : env -> path -> bool
  val is_dtype_ctor  : env -> path -> bool
  val is_fix_def     : env -> path -> bool
  val is_abbrev      : env -> path -> bool
  val is_prind       : env -> path -> bool

  val scheme_of_prind :
    env -> [`Ind | `Case] -> EcPath.path -> (path * int) option

  type notation = ty_params * EcDecl.notation

  val get_notations : env -> (path * notation) list
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

  val decompose_fun : EcTypes.ty -> env -> EcTypes.dom * EcTypes.ty

  val scheme_of_ty :
    [`Ind | `Case] -> EcTypes.ty -> env -> (path * EcTypes.ty list) option

  val signature : env -> ty -> ty list * ty
end

val ty_hnorm : ty -> env -> ty

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
  val by_path     : path -> env -> Sp.t
  val lookup      : qsymbol -> env -> path * Sp.t
  val lookup_opt  : qsymbol -> env -> (path * Sp.t) option
  val lookup_path : qsymbol -> env -> path
  val is_base     : qsymbol -> env -> bool

  val add   : symbol -> env -> env
  val addto : path -> path list -> env -> env
end

(* -------------------------------------------------------------------- *)
module Reduction : sig
  type rule   = EcTheory.rule
  type topsym = [ `Path of path | `Tuple ]

  val add1 : path * rule_option * rule option -> env -> env
  val add  : (path * rule_option * rule option) list -> env -> env
  val get  : topsym -> env -> rule list
end

(* -------------------------------------------------------------------- *)
module Auto : sig
  val dname  : symbol
  val add1   : local:bool -> level:int -> ?base:symbol -> path -> env -> env
  val add    : local:bool -> level:int -> ?base:symbol -> path list -> env -> env
  val get    : ?base:symbol -> env -> path list
  val getall : symbol list -> env -> path list
  val getx   : symbol -> env ->  (int * path list) list
end

(* -------------------------------------------------------------------- *)
module AbsStmt : sig
  type t = EcModules.abs_uses

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

(* -------------------------------------------------------------------- *)
open EcBaseLogic

module LDecl : sig
  type error =
  | InvalidKind     of EcIdent.t * [`Variable | `Hypothesis]
  | CannotClear     of EcIdent.t * EcIdent.t
  | NameClash       of [`Ident of EcIdent.t | `Symbol of symbol]
  | LookupError     of [`Ident of EcIdent.t | `Symbol of symbol]

  exception LdeclError of error

  type hyps

  val init    : env -> ?locals:EcBaseLogic.l_local list -> ty_params -> hyps
  val tohyps  : hyps -> EcBaseLogic.hyps
  val toenv   : hyps -> env
  val baseenv : hyps -> env

  val ld_subst  : f_subst -> local_kind -> local_kind
  val add_local : EcIdent.t -> local_kind -> hyps -> hyps

  val by_name : symbol    -> hyps -> l_local
  val by_id   : EcIdent.t -> hyps -> local_kind

  val has_name : symbol    -> hyps -> bool
  val has_id   : EcIdent.t -> hyps -> bool

  val as_var : l_local -> EcIdent.t * ty
  val as_hyp : l_local -> EcIdent.t * form

  val hyp_by_name : symbol    -> hyps -> EcIdent.t * form
  val hyp_exists  : symbol    -> hyps -> bool
  val hyp_by_id   : EcIdent.t -> hyps -> form

  val var_by_name : symbol    -> hyps -> EcIdent.t * ty
  val var_exists  : symbol    -> hyps -> bool
  val var_by_id   : EcIdent.t -> hyps -> ty

  val local_hyps  : EcIdent.t -> hyps -> hyps

  val hyp_convert :
       EcIdent.t
    -> (hyps Lazy.t -> form -> form)
    -> hyps
    -> hyps option

  val can_unfold : EcIdent.t -> hyps -> bool
  val unfold     : EcIdent.t -> hyps -> form

  val fresh_id  : hyps -> symbol -> EcIdent.t
  val fresh_ids : hyps -> symbol list -> EcIdent.t list

  val clear : ?leniant:bool -> EcIdent.Sid.t -> hyps -> hyps

  val push_all    : memenv list -> hyps -> hyps
  val push_active : memenv -> hyps -> hyps

  val hoareF : xpath -> hyps -> hyps * hyps
  val equivF : xpath -> xpath -> hyps -> hyps * hyps

  val inv_memenv  : hyps -> hyps
  val inv_memenv1 : hyps -> hyps
end
