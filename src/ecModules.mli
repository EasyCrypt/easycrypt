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
(* LvMap (op, m, x, ty)
 * - op is the map-set operator
 * - m  is the map to be updated
 * - x  is the index to update
 * - ty is the type of the value [m] *)
type lvmap = (path * ty list) *  prog_var * expr * ty

type lvalue =
  | LvVar   of (prog_var * ty)
  | LvTuple of (prog_var * ty) list
  | LvMap   of lvmap

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

val fs_equal : funsig -> funsig -> bool
(* -------------------------------------------------------------------- *)
type 'a use_restr = {
  ur_pos : 'a option;   (* If not None, can use only element in this set. *)
  ur_neg : 'a;          (* Cannot use element in this set. *)
}

val ur_empty : 'a -> 'a use_restr
val ur_full  : 'a -> 'a use_restr
val ur_app   : ('a -> 'b) -> 'a use_restr -> 'b use_restr
val ur_equal : ('a -> 'a -> bool) -> 'a use_restr -> 'a use_restr -> bool

(* Correctly handles the [None] cases for subset comparison. *)
val ur_pos_subset : ('a -> 'a -> bool) -> 'a option -> 'a option -> bool
val ur_union :
  ('a -> 'a -> 'a) ->
  ('a -> 'a -> 'a) ->
  'a use_restr -> 'a use_restr -> 'a use_restr

(* -------------------------------------------------------------------- *)
(* [oi_calls]: The list of oracle that can be called
 * [oi_in]: true if equality of globals is required to ensure
 * equality of result and globals
*)
type oracle_info = {
  oi_calls : xpath list;
  oi_in    : bool;
}

val oi_empty : oracle_info
val oi_hash  : oracle_info -> int

(* -------------------------------------------------------------------- *)
type mod_restr = {
  mr_xpaths : EcPath.Sx.t use_restr;
  mr_mpaths : EcPath.Sm.t use_restr;
  mr_oinfos : oracle_info Msym.t;
}

(* Careful, the avalaible oracle are empty in both [mr_empty] and [mr_full]. *)
val mr_empty : mod_restr
val mr_full  : mod_restr

val mr_hash  : mod_restr -> int
val mr_equal : mod_restr -> mod_restr -> bool

val mr_add_restr :
  mod_restr -> EcPath.Sx.t use_restr -> EcPath.Sm.t use_restr -> mod_restr

val add_oinfo      : mod_restr -> string -> xpath list -> bool -> mod_restr
val change_oicalls : mod_restr -> string -> xpath list -> mod_restr
val oicalls_filter :
  mod_restr ->
  EcSymbols.Msym.key ->
  (EcPath.xpath -> bool) ->
  mod_restr

(* -------------------------------------------------------------------- *)
(* An oracle in a function provided by a module parameter of a functor *)

type module_type = {                   (* Always in eta-normal form *)
  mt_params : (EcIdent.t * module_type) list;
  mt_name   : EcPath.path;
  mt_args   : EcPath.mpath list;
  mt_restr  : mod_restr;
}


type module_sig_body_item =
| Tys_function of funsig

type module_sig_body = module_sig_body_item list

type module_sig = {
  mis_params : (EcIdent.t * module_type) list;
  mis_body   : module_sig_body;
  mis_restr : mod_restr;
}

(* Simple module signature, without restrictions. *)
type module_smpl_sig = {
  miss_params : (EcIdent.t * module_type) list;
  miss_body   : module_sig_body;
}

val sig_smpl_sig_coincide : module_sig -> module_smpl_sig -> bool
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
type module_expr = {
  me_name     : symbol;
  me_body     : module_body;
  me_comps    : module_comps;
  me_sig_body : module_sig_body;
  me_params   : (EcIdent.t * module_type) list;
}

and module_body =
  | ME_Alias       of int * EcPath.mpath
                      (* The int represent the number of argument *)
  | ME_Structure   of module_structure
  | ME_Decl        of module_type

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

val mty_subst :
  (path -> path) ->
  (mpath -> mpath) ->
  (xpath -> xpath) ->
  module_type ->
  module_type

val mty_equal : module_type -> module_type -> bool
val mty_hash  : module_type -> int

(* -------------------------------------------------------------------- *)
val get_uninit_read_of_fun : xpath -> function_ -> Sx.t
val get_uninit_read_of_module : path -> module_expr -> (xpath * Sx.t) list
