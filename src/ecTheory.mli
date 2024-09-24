(* -------------------------------------------------------------------- *)
open EcSymbols
open EcPath
open EcAst
open EcTypes
open EcDecl
open EcModules

(* -------------------------------------------------------------------- *)
type import = { im_immediate : bool; im_atimport : bool; }

val import0  : import
val noimport : import

(* -------------------------------------------------------------------- *)
type theory = theory_item list

and theory_item = {
  ti_item   : theory_item_r;
  ti_import : import;
}

and theory_item_r =
  | Th_type      of (symbol * tydecl)
  | Th_operator  of (symbol * operator)
  | Th_axiom     of (symbol * axiom)
  | Th_modtype   of (symbol * top_module_sig)
  | Th_module    of top_module_expr
  | Th_theory    of (symbol * ctheory)
  | Th_export    of EcPath.path * is_local
  | Th_instance  of (ty_params * EcTypes.ty) * tcinstance * is_local
  | Th_typeclass of (symbol * typeclass)
  | Th_baserw    of symbol * is_local
  | Th_addrw     of EcPath.path * EcPath.path list * is_local
  (* reduction rule does not survive to section so no locality *)
  | Th_reduction of (EcPath.path * rule_option * rule option) list
  | Th_auto      of (int * symbol option * path list * is_local)

and thsource = {
  ths_base : EcPath.path;
}

and ctheory = {
  cth_items  : theory;
  cth_mode   : thmode;
  cth_loca   : is_local;
  cth_source : thsource option;
}

and tcinstance = [ `Ring of ring | `Field of field | `General of EcPath.path ]
and thmode     = [ `Abstract | `Concrete ]

and rule_pattern =
  | Rule of top_rule_pattern * rule_pattern list
  | Int  of EcBigInt.zint
  | Var  of EcIdent.t

and top_rule_pattern =
  [`Op of (EcPath.path * EcTypes.ty list) | `Tuple | `Proj of int]

and rule = {
  rl_tyd   : EcDecl.ty_params;
  rl_vars  : (EcIdent.t * EcTypes.ty) list;
  rl_cond  : EcCoreFol.form list;
  rl_ptn   : rule_pattern;
  rl_tg    : EcCoreFol.form;
  rl_prio  : int;
}

and rule_option = {
  ur_delta  : bool;
  ur_eqtrue : bool;
}

val mkitem : import -> theory_item_r -> theory_item

(* -------------------------------------------------------------------- *)
val module_expr_of_module_sig : EcIdent.t -> mty_mr -> module_sig -> module_expr
