(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcDecl
(* -------------------------------------------------------------------- *)
type modifier = [ `Use | `Read | `Write ]

type tymod =
  | Tym_sig     of tysig
  | Tym_functor of (EcIdent.t * tymod) list * tysig

and tysig = tysig_item list

and tysig_item =
  | Tys_variable of symbol * EcTypes.ty
  | Tys_function of funsig

and funsig = {
  fs_name : symbol;
  fs_sig  : (EcIdent.t * EcTypes.ty) list * EcTypes.ty;
  fs_uses : (EcPath.path * modifier) list;
}

(* -------------------------------------------------------------------- *)
type module_expr = {
  me_name       : EcIdent.t;
  me_body       : module_body;
  me_components : module_components Lazy.t;
  me_sig        : tymod
}

and module_body =
  | ME_Ident       of EcPath.path
  | ME_Application of EcPath.path * EcPath.path list
  | ME_Structure   of module_structure
  | ME_Decl        of EcPath.path

and module_structure = {
  ms_params : (EcIdent.t * tymod) list;
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
  f_locals : (EcIdent.t * EcTypes.ty) list;
  f_body   : stmt;                      (* FIXME *)
  f_ret    : EcTypes.tyexpr option;
}

and variable = {
  v_name : EcIdent.t;
  v_type : EcTypes.ty;
}

and stmt = instr list

and instr =
  | Sasgn   of lvalue * EcTypes.tyexpr
  | Scall   of lvalue option * EcPath.path * EcTypes.tyexpr list
  | Sif     of EcTypes.tyexpr * stmt * stmt
  | Swhile  of EcTypes.tyexpr * stmt
  | Sassert of EcTypes.tyexpr

and lvalue =
  | LvVar   of (EcPath.path * EcTypes.ty)
  | LvTuple of (EcPath.path * EcTypes.ty) list
  | LvMap   of EcPath.path * EcPath.path * EcTypes.tyexpr * EcTypes.ty
               (* op, map, where, type updated value *)

(* -------------------------------------------------------------------- *)
type theory = theory_item list

and theory_item =
  | Th_type      of (EcIdent.t * tydecl)
  | Th_operator  of (EcIdent.t * operator)
  | Th_axiom     of (EcIdent.t * axiom)
  | Th_modtype   of (EcIdent.t * tymod)
  | Th_module    of module_expr
  | Th_theory    of (EcIdent.t * theory)
  | Th_export    of EcPath.path

(* -------------------------------------------------------------------- *)
type ctheory = {
  cth_desc   : ctheory_desc;
  cth_struct : ctheory_struct;
}

and ctheory_desc =
  | CTh_struct of ctheory_struct
  | CTh_clone  of EcPath.path

and ctheory_struct = ctheory_item list

and ctheory_item =
  | CTh_type      of (EcIdent.t * tydecl)
  | CTh_operator  of (EcIdent.t * operator)
  | CTh_axiom     of (EcIdent.t * axiom)
  | CTh_modtype   of (EcIdent.t * tymod)
  | CTh_module    of module_expr
  | CTh_theory    of (EcIdent.t * ctheory)
  | CTh_export    of EcPath.path
