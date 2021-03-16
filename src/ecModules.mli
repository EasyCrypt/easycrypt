(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcSymbols
open EcPath
open EcTypes

(* -------------------------------------------------------------------- *)
type lvalue =
  | LvVar   of (prog_var * ty)
  | LvTuple of (prog_var * ty) list

val lv_equal     : lvalue -> lvalue -> bool
val symbol_of_lv : lvalue -> symbol
val ty_of_lv     : lvalue -> EcTypes.ty

(* --------------------------------------------------------------------- *)
type instr = private {
  i_node : instr_node;
  i_fv   : int EcIdent.Mid.t;
  i_tag  : int;
}

and instr_node =
  | Sasgn     of lvalue * expr
  | Srnd      of lvalue * expr
  | Scall     of lvalue option * xpath * expr list
  | Sif       of expr * stmt * stmt
  | Swhile    of expr * stmt
  | Sassert   of expr
  | Sabstract of EcIdent.t

and stmt = private {
  s_node : instr list;
  s_fv   : int EcIdent.Mid.t;
  s_tag  : int;
}

(* -------------------------------------------------------------------- *)
val i_equal   : instr -> instr -> bool
val i_compare : instr -> instr -> int
val i_hash    : instr -> int
val i_fv      : instr -> int EcIdent.Mid.t
val i_node    : instr -> instr_node

val s_equal   : stmt -> stmt -> bool
val s_compare : stmt -> stmt -> int
val s_hash    : stmt -> int
val s_fv      : stmt -> int EcIdent.Mid.t
val s_subst   : e_subst -> stmt -> stmt

(* -------------------------------------------------------------------- *)
val i_asgn     : lvalue * expr -> instr
val i_rnd      : lvalue * expr -> instr
val i_call     : lvalue option * xpath * expr list -> instr
val i_if       : expr * stmt * stmt -> instr
val i_while    : expr * stmt -> instr
val i_assert   : expr -> instr
val i_abstract : EcIdent.t -> instr

val s_asgn     : lvalue * expr -> stmt
val s_rnd      : lvalue * expr -> stmt
val s_call     : lvalue option * xpath * expr list -> stmt
val s_if       : expr * stmt * stmt -> stmt
val s_while    : expr * stmt -> stmt
val s_assert   : expr -> stmt
val s_abstract : EcIdent.t -> stmt
val s_seq      : stmt -> stmt -> stmt
val s_empty    : stmt

val stmt  : instr list -> stmt
val rstmt : instr list -> stmt

(* the following functions raise Not_found if the argument does not match *)
val destr_asgn   : instr -> lvalue * expr
val destr_rnd    : instr -> lvalue * expr
val destr_call   : instr -> lvalue option * xpath * expr list
val destr_if     : instr -> expr * stmt * stmt
val destr_while  : instr -> expr * stmt
val destr_assert : instr -> expr

val is_asgn   : instr -> bool
val is_rnd    : instr -> bool
val is_call   : instr -> bool
val is_if     : instr -> bool
val is_while  : instr -> bool
val is_assert : instr -> bool

(* -------------------------------------------------------------------- *)
val get_uninit_read : stmt -> Sx.t

(* -------------------------------------------------------------------- *)
type variable = {
  v_name : symbol;
  v_type : EcTypes.ty;
}

val v_name : variable -> symbol
val v_type : variable -> EcTypes.ty

(* -------------------------------------------------------------------- *)
type funsig = {
  fs_name   : symbol;
  fs_arg    : EcTypes.ty;
  fs_anames : variable list option;
  fs_ret    : EcTypes.ty;
}

(* -------------------------------------------------------------------- *)
(* An oracle in a function provided by a module parameter of a functor *)

type module_type = {                   (* Always in eta-normal form *)
  mt_params : (EcIdent.t * module_type) list;
  mt_name   : EcPath.path;
  mt_args   : EcPath.mpath list;
}

(* [oi_calls]: The list of oracle that can be called
 * [oi_in]: true if equality of globals is required to ensure
 * equality of result and globals
*)
type oracle_info = {
  oi_calls : xpath list;
  oi_in    : bool;
}

type module_sig_body_item =
(* oracle_info contain only function provided by the module parameters *)
| Tys_function of funsig * oracle_info

type module_sig_body = module_sig_body_item list

type module_sig = {
  mis_params : (EcIdent.t * module_type) list;
  mis_body   : module_sig_body;
}

(* -------------------------------------------------------------------- *)
type uses = private {
  us_calls  : xpath list;
  us_reads  : Sx.t;
  us_writes : Sx.t;
}

val mk_uses : xpath list -> Sx.t -> Sx.t -> uses

type function_def = {
  f_locals : variable list;
  f_body   : stmt;
  f_ret    : EcTypes.expr option;
  f_uses   : uses;
}

type function_body =
  | FBdef   of function_def
  | FBalias of xpath
  | FBabs   of oracle_info

type function_ = {
  f_name   : symbol;
  f_sig    : funsig;
  f_def    : function_body;
}

(* -------------------------------------------------------------------- *)
type abs_uses = {
  aus_calls  : EcPath.xpath list;
  aus_reads  : (prog_var * ty) list;
  aus_writes : (prog_var * ty) list;
}

(* -------------------------------------------------------------------- *)
type mod_restr = EcPath.Sx.t * EcPath.Sm.t

val mr_equal : mod_restr -> mod_restr -> bool

(* -------------------------------------------------------------------- *)
type module_expr = {
  me_name  : symbol;
  me_body  : module_body;
  me_comps : module_comps;
  me_sig   : module_sig;
}

and module_body =
  | ME_Alias       of int * EcPath.mpath
                      (* The int represent the number of argument *)
  | ME_Structure   of module_structure
  | ME_Decl        of module_type * mod_restr

(* [ms_vars]: the set of global variables declared by the module and
 * all it submodules.
 *
 * [ms_uses]: the set of external top-level modules used by the module
 * We ensure that these paths lead to defined modules (i.e having
 * ME_structure as body)
 *)
and module_structure = {
  ms_body : module_item list;
}

and module_item =
| MI_Module   of module_expr
| MI_Variable of variable
| MI_Function of function_

and module_comps = module_comps_item list

and module_comps_item = module_item

(* -------------------------------------------------------------------- *)
val fd_equal : function_def -> function_def -> bool
val fd_hash  : function_def -> int

val mty_subst : (path -> path) -> (mpath -> mpath) -> module_type -> module_type

val mty_equal : module_type -> module_type -> bool
val mty_hash  : module_type -> int

(* -------------------------------------------------------------------- *)
val get_uninit_read_of_fun : xpath -> function_ -> Sx.t
val get_uninit_read_of_module : path -> module_expr -> (xpath * Sx.t) list
