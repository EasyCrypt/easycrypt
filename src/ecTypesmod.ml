(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcDecl

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
end = struct
  (* TODO: to be rewritten using -pxp OCaml 4.0 feature *)

  type flag  = [`Call | `Read | `Write]
  type flags = UseFlags of int

  let iflag = function (* (Obj.magic x : int) *)
    | `Call  -> 0
    | `Read  -> 1
    | `Write -> 2

  let empty = UseFlags 0

  let add (UseFlags f : flags) (e : flag) =
    UseFlags (f lor (1 lsl (iflag e)))

  let have (UseFlags f : flags) (e : flag) =
    (f land (1 lsl (iflag e))) != 0

  let singleton (e : flag) =
    add empty e

  let equal (UseFlags fin) (UseFlags fout) =
    fin == fout

  let included (UseFlags fin) (UseFlags fout) =
    (lnot fin) land fout == 0
end

type use_flags = UM.flags

(* -------------------------------------------------------------------- *)
type tymod = {
  tym_params : (EcIdent.t * tymod) list;
  tym_sig    : tysig;
  tym_mforb  : EcPath.Sp.t;
}

and tysig = tysig_item list

and tysig_item =
  | Tys_variable of (symbol * EcTypes.ty)
  | Tys_function of funsig

and funsig = {
  fs_name : symbol;
  fs_sig  : (EcIdent.t * EcTypes.ty) list * EcTypes.ty;
  fs_uses : use_flags EcPath.Mp.t;
}

(* -------------------------------------------------------------------- *)
type module_expr = {
  me_name : EcIdent.t;
  me_body : module_body;
  me_meta : module_meta option;
  me_sig  : tymod;
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

and module_item =
  | MI_Module   of module_expr
  | MI_Variable of variable
  | MI_Function of function_

and module_components = module_components_item list

and module_components_item = module_item

and module_meta = {
  mm_components : module_components option;
  mm_uses       : EcPath.Sp.t;
}

and function_ = {
  f_name   : EcIdent.t;
  f_sig    : funsig;
  f_locals : (EcIdent.t * EcTypes.ty) list;
  f_body   : stmt;
  f_ret    : EcTypes.tyexpr option;
}

and variable = {
  v_name : EcIdent.t;
  v_type : EcTypes.ty;
}

and stmt = instr list

and instr =
  | Sasgn   of lvalue * EcTypes.tyexpr
  | Srnd    of lvalue * EcTypes.tyexpr
  | Scall   of lvalue option * EcPath.path * EcTypes.tyexpr list
  | Sif     of EcTypes.tyexpr * stmt * stmt
  | Swhile  of EcTypes.tyexpr * stmt
  | Sassert of EcTypes.tyexpr

and lvalue =
  | LvVar   of (EcTypes.prog_var * EcTypes.ty)
  | LvTuple of (EcTypes.prog_var * EcTypes.ty) list
  | LvMap   of (EcPath.path * EcTypes.ty list) * 
               EcTypes.prog_var * EcTypes.tyexpr * EcTypes.ty
 (* LvMap(op, m, x, ty)
    - op is the set operator
    - m is the map to be updated 
    - x is the position to update
    - ty is the type of the value associated to x *)

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
  | CTh_clone  of ctheory_clone

and ctheory_struct = ctheory_item list

and ctheory_item =
  | CTh_type      of (EcIdent.t * tydecl)
  | CTh_operator  of (EcIdent.t * operator)
  | CTh_axiom     of (EcIdent.t * axiom)
  | CTh_modtype   of (EcIdent.t * tymod)
  | CTh_module    of module_expr
  | CTh_theory    of (EcIdent.t * ctheory)
  | CTh_export    of EcPath.path

and ctheory_clone = {
  cthc_base : EcPath.path;
  cthc_ext  : (EcIdent.t * ctheory_override) list;
}

and ctheory_override =
| CTHO_Type   of EcTypes.ty
| CTHO_Module of EcPath.path * (EcPath.path list)
