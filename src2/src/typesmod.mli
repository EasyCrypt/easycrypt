(* -------------------------------------------------------------------- *)
open Utils
open Symbols

(* -------------------------------------------------------------------- *)
type modifier = [ `Use | `Read | `Write ]

type tymod =
  | Tym_sig     of tysig
  | Tym_functor of (Ident.t * tymod) list * tymod

and tysig = tysig_item list

and tysig_item =
  | Tys_variable of symbol * Types.ty
  | Tys_function of funsig

and funsig = {
  fs_name : symbol;
  fs_sig  : (Ident.t * Types.ty) list * Types.ty;
  fs_uses : (Path.path * modifier) list;
}

(* -------------------------------------------------------------------- *)
type module_expr = {
  me_name       : Ident.t;
  me_body       : module_body;
  me_components : module_components Lazy.t;
  me_sig        : tymod
}

and module_body =
  | ME_Ident       of Path.path
  | ME_Application of Path.path * Path.path list
  | ME_Structure   of module_structure
  | ME_Decl        of Path.path

and module_structure = {
  ms_params : (Ident.t * tymod) list;
  ms_body   : module_item list;
}

and module_item = [
  | `Module   of module_expr
  | `Variable of variable
  | `Function of function_
]

and module_components = module_components_item list

and module_components_item = module_item

and function_ = {
  f_sig    : funsig;
  f_locals : (Ident.t * Types.ty) list;
  f_body   : unit;                      (* FIXME *)
}

and variable = {
  v_name : Ident.t;
  v_type : Types.ty;
}

and stmt = instr list

and instr =
  | Sasgn   of lvalue * Path.path * Types.tyexpr list
  | Scall   of lvalue option * Path.path * Types.tyexpr list
  | Sif     of Types.tyexpr * stmt * stmt
  | Swhile  of Types.tyexpr * stmt
  | Sassert of Types.tyexpr

and lvalue =
  | LvVar   of (Path.path * Types.ty)
  | LvTuple of (Path.path * Types.ty) Parray.t
  | LvMap   of Path.path * Types.tyexpr * Types.ty

(* -------------------------------------------------------------------- *)
type axiom = {
  ax_name : symbol;
  ax_spec : unit;                       (* formula *)
}

(* -------------------------------------------------------------------- *)
type operator = {
  op_sig  : Types.ty list * Types.ty;
  op_ctnt : bool;
  op_prob : bool;
}

(* -------------------------------------------------------------------- *)
type tydecl = {
  tyd_params : int;
  tyd_type   : Types.ty option;
}
