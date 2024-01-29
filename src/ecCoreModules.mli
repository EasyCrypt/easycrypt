(* -------------------------------------------------------------------- *)
open EcSymbols
open EcPath
open EcTypes

(* -------------------------------------------------------------------- *)
type lvalue = EcAst.lvalue

val lv_equal     : lvalue -> lvalue -> bool
val symbol_of_lv : lvalue -> symbol
val ty_of_lv     : lvalue -> EcTypes.ty
val lv_of_list   : (prog_var * ty) list -> lvalue option
val lv_to_list   : lvalue -> prog_var list
val name_of_lv   : lvalue -> string
val lv_of_expr   : expr -> lvalue

(* --------------------------------------------------------------------- *)
type instr = EcAst.instr

type instr_node = EcAst.instr_node

type stmt = EcAst.stmt

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

(* -------------------------------------------------------------------- *)
val i_asgn     : lvalue * expr -> instr
val i_rnd      : lvalue * expr -> instr
val i_call     : lvalue option * xpath * expr list -> instr
val i_if       : expr * stmt * stmt -> instr
val i_while    : expr * stmt -> instr
val i_match    : expr * ((EcIdent.t * ty) list * stmt) list -> instr
val i_assert   : expr -> instr
val i_abstract : EcIdent.t -> instr

val s_asgn     : lvalue * expr -> stmt
val s_rnd      : lvalue * expr -> stmt
val s_call     : lvalue option * xpath * expr list -> stmt
val s_if       : expr * stmt * stmt -> stmt
val s_while    : expr * stmt -> stmt
val s_match    : expr * ((EcIdent.t * ty) list * stmt) list -> stmt
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
val destr_match  : instr -> expr * ((EcIdent.t * ty) list * stmt) list
val destr_assert : instr -> expr

val is_asgn   : instr -> bool
val is_rnd    : instr -> bool
val is_call   : instr -> bool
val is_if     : instr -> bool
val is_while  : instr -> bool
val is_match  : instr -> bool
val is_assert : instr -> bool

(* -------------------------------------------------------------------- *)
val get_uninit_read : stmt -> Sx.t

(* -------------------------------------------------------------------- *)
type funsig = {
  fs_name   : symbol;
  fs_arg    : EcTypes.ty;
  fs_anames : ovariable list;
  fs_ret    : EcTypes.ty;
}

val fs_equal : funsig -> funsig -> bool

(* -------------------------------------------------------------------- *)
type 'a use_restr = 'a EcAst.use_restr

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
(* Oracle information of a procedure [M.f]. *)
module PreOI : sig
  type t = EcAst.oracle_info

  val hash : t -> int
  val equal : (EcAst.form -> EcAst.form -> bool) -> t -> t -> bool

  val cost_self : t -> [`Bounded of EcAst.form | `Unbounded]
  val cost : t -> xpath -> [`Bounded of EcAst.form | `Zero | `Unbounded]
  val cost_calls : t -> [`Bounded of EcAst.form Mx.t | `Unbounded]
  val costs : t -> [`Bounded of EcAst.form * EcAst.form Mx.t | `Unbounded]

  val allowed : t -> xpath list
  val allowed_s : t -> Sx.t

  val mk : xpath list -> [`Bounded of EcAst.form * EcAst.form Mx.t | `Unbounded] -> t
  val filter : (xpath -> bool) -> t -> t
end

(* -------------------------------------------------------------------- *)
type mr_xpaths = EcAst.mr_xpaths

type mr_mpaths = EcAst.mr_mpaths

type mod_restr = EcAst.mod_restr

val mr_equal :
  mod_restr ->
  mod_restr ->
  bool

val mr_hash : mod_restr -> int

val has_compl_restriction : mod_restr -> bool

val mr_is_empty : mod_restr -> bool

val mr_xpaths_fv : mr_xpaths -> int EcIdent.Mid.t
val mr_mpaths_fv : mr_mpaths -> int EcIdent.Mid.t

(* -------------------------------------------------------------------- *)
(* An oracle in a function provided by a module parameter of a functor *)
type module_type = EcAst.module_type

type module_sig_body_item = Tys_function of funsig

type module_sig_body = module_sig_body_item list

type module_sig = {
  mis_params : (EcIdent.t * module_type) list;
  mis_body   : module_sig_body;
  mis_restr  : mod_restr;
}

type top_module_sig = {
  tms_sig  : module_sig;
  tms_loca : is_local;
}

(* -------------------------------------------------------------------- *)
(* Simple module signature, without restrictions. *)
type module_smpl_sig = {
  miss_params : (EcIdent.t * module_type) list;
  miss_body   : module_sig_body;
}

val sig_smpl_sig_coincide : module_sig -> module_smpl_sig -> bool

(* -------------------------------------------------------------------- *)
type uses = {
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

val fd_equal : function_def -> function_def -> bool
val fd_hash  : function_def -> int

(* -------------------------------------------------------------------- *)
type function_body =
| FBdef   of function_def
| FBalias of xpath
| FBabs   of PreOI.t

type function_ = {
  f_name   : symbol;
  f_sig    : funsig;
  f_def    : function_body;
}

(* -------------------------------------------------------------------- *)
type abs_uses = {
  aus_calls  : EcPath.xpath list;
  aus_reads  : (EcTypes.prog_var * EcTypes.ty) list;
  aus_writes : (EcTypes.prog_var * EcTypes.ty) list;
}

type module_expr = {
  me_name     : symbol;
  me_body     : module_body;
  me_comps    : module_comps;
  me_sig_body : module_sig_body;
  me_params   : (EcIdent.t * module_type) list;
}

(* Invariant:
   In an abstract module [ME_Decl mt], [mt] must not be a functor, i.e. it must
   be fully applied. Therefore, we must have:
   [List.length mp.mt_params = List.length mp.mt_args]  *)
and module_body =
  | ME_Alias       of int * EcPath.mpath
  | ME_Structure   of module_structure       (* Concrete modules. *)
  | ME_Decl        of module_type         (* Abstract modules. *)

and module_structure = {
  ms_body      : module_item list;
}

and module_item =
  | MI_Module   of module_expr
  | MI_Variable of variable
  | MI_Function of function_

and module_comps = module_comps_item list

and module_comps_item = module_item

type top_module_expr = {
  tme_expr : module_expr;
  tme_loca : locality;
}

(* -------------------------------------------------------------------- *)
val mty_equal :
  module_type ->
  module_type ->
  bool

val mty_hash : module_type -> int

(* -------------------------------------------------------------------- *)
val get_uninit_read : stmt -> Ssym.t
val get_uninit_read_of_fun : function_ -> Ssym.t
val get_uninit_read_of_module : path -> module_expr -> (xpath * Ssym.t) list
