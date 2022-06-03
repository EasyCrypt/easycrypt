(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcPath
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
  | Th_schema    of (symbol * ax_schema)
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
  | Cost of EcMemory.memenv * rule_pattern * rule_pattern (* memenv, pre, expr *)
  | Int  of EcBigInt.zint
  | Var  of EcIdent.t

and top_rule_pattern =
  [`Op of (EcPath.path * EcTypes.ty list) | `Tuple]

and rule = {
  rl_tyd   : EcDecl.ty_params;
  rl_vars  : (EcIdent.t * EcTypes.ty) list;
  rl_evars : (EcIdent.t * EcTypes.ty) list;
  rl_pvars : EcIdent.t list;
  rl_cond  : EcCoreFol.form list;
  rl_ptn   : rule_pattern;
  rl_tg    : EcCoreFol.form;
  rl_prio  : int;
}

and rule_option = {
  ur_delta  : bool;
  ur_eqtrue : bool;
  ur_mode   : [`Ax | `Sc];
}

let mkitem (import : import) (item : theory_item_r) =
  { ti_import = import; ti_item = item; }

(* -------------------------------------------------------------------- *)
let module_comps_of_module_sig_comps (comps : module_sig_body) restr =
  let onitem = function
    | Tys_function funsig ->
      let oi = Msym.find funsig.fs_name restr.mr_oinfos in
        MI_Function {
          f_name = funsig.fs_name;
          f_sig  = funsig;
          f_def  = FBabs oi;
        }
  in
    List.map onitem comps

(* -------------------------------------------------------------------- *)
let module_expr_of_module_sig name mp tymod =
  (* Abstract modules must be fully applied. *)
  assert (List.length mp.mt_params = List.length mp.mt_args);

  let tycomps = module_comps_of_module_sig_comps tymod.mis_body mp.mt_restr in
    { me_name     = EcIdent.name name;
      me_body     = ME_Decl mp;
      me_comps    = tycomps;
      me_sig_body = tymod.mis_body;
      me_params   = tymod.mis_params ; }
