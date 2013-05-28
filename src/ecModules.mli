(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcPath
open EcTypes

(* -------------------------------------------------------------------- *)
(* LvMap (op, m, x, ty)
 * - op is the map-set operator
 * - m  is the map to be updated 
 * - x  is the index to update
 * - ty is the type of the value [m] *)
type lvalue =
  | LvVar   of (EcTypes.prog_var * EcTypes.ty)
  | LvTuple of (EcTypes.prog_var * EcTypes.ty) list
  | LvMap   of (EcPath.path * EcTypes.ty list) * 
                  EcTypes.prog_var * EcTypes.expr * EcTypes.ty

val lv_equal : lvalue -> lvalue -> bool
val symbol_of_lv : lvalue -> symbol

(* --------------------------------------------------------------------- *)
type instr = private {
  i_node : instr_node;
  i_fv   : int EcIdent.Mid.t;
  i_tag  : int;
}

and instr_node =
  | Sasgn   of lvalue * EcTypes.expr
  | Srnd    of lvalue * EcTypes.expr
  | Scall   of lvalue option * EcPath.xpath * EcTypes.expr list
  | Sif     of EcTypes.expr * stmt * stmt
  | Swhile  of EcTypes.expr * stmt
  | Sassert of EcTypes.expr

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

val s_equal   : stmt -> stmt -> bool
val s_compare : stmt -> stmt -> int
val s_hash    : stmt -> int
val s_fv      : stmt -> int EcIdent.Mid.t
val s_subst   : e_subst -> stmt -> stmt 

(* -------------------------------------------------------------------- *)
val i_asgn    : lvalue * expr -> instr
val i_rnd     : lvalue * expr -> instr
val i_call    : lvalue option * xpath * expr list -> instr
val i_if      : expr * stmt * stmt -> instr
val i_while   : expr * stmt -> instr
val i_assert  : expr -> instr

val stmt : instr list -> stmt
(* [rstmt l] is stmt (List.rev l) *)
val rstmt : instr list -> stmt

val s_split : int -> stmt -> instr list * instr list

(* the following functions raise Not_found if the argument does not match *) 
val destr_asgn   : instr -> lvalue * expr
val destr_rnd    : instr -> lvalue * expr
val destr_call   : instr -> lvalue option * xpath * expr list
val destr_if     : instr -> expr * stmt * stmt
val destr_while  : instr -> expr * stmt
val destr_assert : instr -> expr

(* -------------------------------------------------------------------- *)
type variable = {
  v_name : symbol;
  v_type : EcTypes.ty;
}

type funsig = {
  fs_name   : symbol;
  fs_params : variable list;
  fs_ret    : EcTypes.ty;
}

(* -------------------------------------------------------------------- *)

(* An oracle in a function provided by a module parameter of a functor *)

type module_type = {                   (* Always in eta-normal form *)
  mt_params : (EcIdent.t * module_type) list;
  mt_name   : EcPath.path;
  mt_args   : EcPath.mpath list;
}

type oracle_info = {
  oi_calls  : xpath list; (* The list of oracle that can be called *)
(*  oi_reads  : Sx.t;   (* The list of global prog var of the outside word *)
  oi_writes : Sx.t;     (* that can be read only or read and write *) *)
}

type module_sig_body_item =
(*  | Tys_variable of variable *)
  | Tys_function of funsig * oracle_info
           (* oracle_info contain only function provided by the 
              module parameters *)

type module_sig_body = module_sig_body_item list

type module_sig = {
  mis_params : (EcIdent.t * module_type) list;
  mis_body   : module_sig_body;
}

(* -------------------------------------------------------------------- *)
type uses = {
  us_calls  : xpath list;
  us_reads  : Sx.t;
  us_writes : Sx.t;
}

type function_def = {
  f_locals : variable list;
  f_body   : stmt;
  f_ret    : EcTypes.expr option;
  f_uses   : uses;
}

type function_body =
| FBdef of function_def
| FBabs of oracle_info

type function_ = {
  f_name   : symbol;
  f_sig    : funsig;
  f_def    : function_body;
}

(* -------------------------------------------------------------------- *)

type module_expr = {
  me_name      : symbol;
  me_body      : module_body;
  me_comps     : module_comps;
  me_sig       : module_sig; 
(*  me_types     : module_type list; *)
}

and module_body =
  | ME_Alias       of EcPath.mpath
  | ME_Structure   of module_structure
  | ME_Decl        of module_type * EcPath.Sm.t 

and module_structure = {
  ms_body   : module_item list;
  ms_vars   : ty Mx.t; (* The set of global variables declared by the
                          module and it submodules *)
  ms_uses : Sm.t; (* The set of external top-level modules used by the module.
                     It is an invariant that those modules are defined 
                     (i.e are ME_structure). *)
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
  (path -> path) -> (mpath -> mpath) ->  module_type -> module_type

val mty_equal : module_type -> module_type -> bool
val mty_hash  : module_type -> int
