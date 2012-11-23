(* -------------------------------------------------------------------- *)
open Symbols

(* -------------------------------------------------------------------- *)
type modifier = [ `Use | `Read | `Write ]

type tymod =
  | Tym_sig     of tysig
  | Tym_functor of (symbol * tymod) * tymod

and tysig = tysig_item list

and tysig_item =
  | Tys_variable of symbol * Types.ty
  | Tys_function of funsig

and funsig = {
  fs_name : symbol;
  fs_sig  : (symbol * Types.ty) list * Types.ty;
  fs_uses : (Path.path * modifier) list;
}

(* -------------------------------------------------------------------- *)
type module_expr = {
  me_name       : symbol;
  me_body       : module_body;
  me_components : module_components;
  me_sig        : tymod
}

and module_body =
  | ME_Ident       of Path.path
  | ME_Application of Path.path * Path.path list
  | ME_Structure   of module_structure
  | ME_Decl        of Path.path

and module_structure = {
  ms_params : (symbol * tymod);
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
  f_locals : (symbol * Types.ty) list;
  f_body   : unit;                      (* FIXME *)
}

and variable = {
  v_name : symbol;
  v_type : Types.ty;
}

(* -------------------------------------------------------------------- *)
type operator = {
  op_name     : symbol;
  op_typarams : int;
  op_sig      : Types.ty list * Types.ty;
}

type axiom = {
  ax_name : symbol;
  ax_spec : unit;                       (* formula *)
}
