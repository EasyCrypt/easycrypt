(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcPath
open EcAst
open EcTypes
open EcDecl
open EcModules

(* -------------------------------------------------------------------- *)
module Sp = EcPath.Sp

(* -------------------------------------------------------------------- *)
type import = { im_immediate : bool; im_atimport : bool; }

let import0  = { im_immediate =  true; im_atimport =  true; }
let noimport = { im_immediate = false; im_atimport = false; }

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

and tcinstance = [ `Ring of ring | `Field of field | `General of path ]
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

let mkitem (import : import) (item : theory_item_r) =
  { ti_import = import; ti_item = item; }

(* -------------------------------------------------------------------- *)
let module_comps_of_module_sig_comps (comps : module_sig_body) (ois : oracle_infos) =
  let onitem = function
    | Tys_function funsig ->
      let oi = Msym.find funsig.fs_name ois in
        MI_Function {
          f_name = funsig.fs_name;
          f_sig  = funsig;
          f_def  = FBabs oi;
        }
  in
    List.map onitem comps

(* -------------------------------------------------------------------- *)
let module_expr_of_module_sig (name : EcIdent.t) ((mty, mr) : mty_mr) (sig_ : module_sig) =
  (* Abstract modules must be fully applied. *)
  assert (List.length mty.mt_params = List.length mty.mt_args);

  let tycomps = module_comps_of_module_sig_comps sig_.mis_body sig_.mis_oinfos in

  { me_name     = EcIdent.name name;
    me_params   = sig_.mis_params ;
    me_body     = ME_Decl (mty, mr);
    me_comps    = tycomps;
    me_sig_body = sig_.mis_body;
    me_oinfos   = sig_.mis_oinfos; }
