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
 * - ty is the type of the value associated to x *)
type lvalue =
  | LvVar   of (EcTypes.prog_var * EcTypes.ty)
  | LvTuple of (EcTypes.prog_var * EcTypes.ty) list
  | LvMap   of (EcPath.path * EcTypes.ty list) * 
                  EcTypes.prog_var * EcTypes.expr * EcTypes.ty

val lv_equal : lvalue -> lvalue -> bool

(* --------------------------------------------------------------------- *)
type instr = private {
  i_node : instr_node;
  i_fv   : int EcIdent.Mid.t;
  i_tag  : int;
}

and instr_node =
  | Sasgn   of lvalue * EcTypes.expr
  | Srnd    of lvalue * EcTypes.expr
  | Scall   of lvalue option * EcPath.mpath * EcTypes.expr list
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
val i_call    : lvalue option * mpath * expr list -> instr
val i_if      : expr * stmt * stmt -> instr
val i_while   : expr * stmt -> instr
val i_assert  : expr -> instr

val stmt : instr list -> stmt

(* -------------------------------------------------------------------- *)
module UM : sig
  type flag  = [`Call | `Read | `Write]
  type flags

  val empty     : flags
  val singleton : flag -> flags
  val add       : flags -> flag -> flags
  val have      : flags -> flag -> bool
  val equal     : flags -> flags -> bool
  val included  : flags -> flags -> bool
end

type use_flags = UM.flags

(* -------------------------------------------------------------------- *)
type variable = {
  v_name : symbol;
  v_type : EcTypes.ty;
}

type module_type = EcPath.path

type module_sig = {
  mt_params : (EcIdent.t * module_type) list;
  mt_body   : module_sig_body;
  mt_mforb  : EcPath.Sp.t;
}

and module_sig_body = module_sig_body_item list

and module_sig_body_item =
  | Tys_variable of variable
  | Tys_function of funsig

and funsig = {
  fs_name : symbol;
  fs_sig  : variable list * EcTypes.ty;
  fs_uses : use_flags EcPath.Mp.t;
}

(* -------------------------------------------------------------------- *)
type module_expr = {
  me_name  : symbol;
  me_body  : module_body;
  me_comps : module_comps;
  me_sig   : module_sig;
  me_uses  : EcPath.Sp.t;
  me_types : module_type list;
}

and module_body =
  | ME_Alias       of EcPath.mpath
  | ME_Structure   of module_structure
  | ME_Decl        of module_type

and module_structure = {
  ms_params : (EcIdent.t * module_type) list;
  ms_body   : module_item list;
}

and module_item =
  | MI_Module   of module_expr
  | MI_Variable of variable
  | MI_Function of function_

and module_comps = module_comps_item list

and module_comps_item = module_item

and function_ = {
  f_name   : symbol;
  f_sig    : funsig;
  f_def    : function_def option;
}

and function_def = {
  f_locals : variable list;
  f_body   : stmt;
  f_ret    : EcTypes.expr option;
}



(* -------------------------------------------------------------------- *)
val fd_equal : function_def -> function_def -> bool
val fd_hash  : function_def -> int
