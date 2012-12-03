(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols

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
  f_body   : unit;                      (* FIXME *)
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
  | LvTuple of (EcPath.path * EcTypes.ty) Parray.t
  | LvMap   of EcPath.path * EcTypes.tyexpr * EcTypes.ty

(* -------------------------------------------------------------------- *)
type axiom_kind = Axiom | Lemma

type axiom = {
  ax_spec : EcFol.form;                       (* formula *)
  ax_kind : axiom_kind
}

(* -------------------------------------------------------------------- *)
type operator = {
  op_params : int;
  op_sig    : EcTypes.ty list * EcTypes.ty;
  op_ctnt   : bool;
  op_prob   : bool;
}

(* -------------------------------------------------------------------- *)
type tydecl = {
  tyd_params : int;
  tyd_type   : EcTypes.ty option;
}

(* -------------------------------------------------------------------- *)
type theory = theory_item list

and theory_item =
  | Th_type     of EcIdent.t * tydecl
  | Th_operator of EcIdent.t * operator
  | Th_modtype  of EcIdent.t * tymod
  | Th_module   of module_expr
