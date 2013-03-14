(* -------------------------------------------------------------------- *)
open EcDebug
open EcUtils
open EcSymbols
open EcDecl

open EcModules

(* -------------------------------------------------------------------- *)
module Sp = EcPath.Sp

(* -------------------------------------------------------------------- *)
type theory = theory_item list

and theory_item =
  | Th_type      of (symbol * tydecl)
  | Th_operator  of (symbol * operator)
  | Th_axiom     of (symbol * axiom)
  | Th_modtype   of (symbol * module_sig)
  | Th_module    of module_expr
  | Th_theory    of (symbol * theory)
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
  | CTh_type      of (symbol * tydecl)
  | CTh_operator  of (symbol * operator)
  | CTh_axiom     of (symbol * axiom)
  | CTh_modtype   of (symbol * module_sig)
  | CTh_module    of module_expr
  | CTh_theory    of (symbol * ctheory)
  | CTh_export    of EcPath.path

and ctheory_clone = {
  cthc_base : EcPath.path;
  cthc_ext  : (EcIdent.t * ctheory_override) list;
}

and ctheory_override =
| CTHO_Type   of EcTypes.ty

(* -------------------------------------------------------------------- *)
let rec cth_dump (cth : ctheory) =
  dnode "ctheory"
    [dnode "description" [cth_desc_dump cth.cth_desc];
     dnode "structure"   (List.map cthi_dump cth.cth_struct)]

and cth_desc_dump (d : ctheory_desc) =
  match d with
  | CTh_struct cth ->
      dnode "CTh_struct" (List.map cthi_dump cth)

  | CTh_clone cl ->
      dnode "CTh_clone" [cth_clone_dump cl]

and cth_clone_dump (cl : ctheory_clone) =
  dnode "theory-clone"
    ((dleaf "base (%s)" (EcPath.tostring cl.cthc_base)) ::
     (List.map
        (fun (x, ovrd) ->
           dnode (Printf.sprintf "override (%s)" (EcIdent.tostring x))
             [cth_ovrd_dump ovrd])
        cl.cthc_ext))

and cth_ovrd_dump (ovrd : ctheory_override) =
  match ovrd with
  | CTHO_Type ty ->
      dnode "CTHO_Type" [EcTypes.ty_dump ty]

and cthi_dump (item : ctheory_item) =
  match item with
  | CTh_type (x, tyd) ->
      dnode
        (Printf.sprintf "CTh_type (%s)" x)
        [tydecl_dump tyd]

  | CTh_operator (x, op) ->
      dnode
        (Printf.sprintf "CTh_operator (%s)" x)
        [op_dump op]

  | CTh_axiom (x, ax) ->
      dnode
        (Printf.sprintf "CTh_axiom (%s)" x)
        [ax_dump ax]

  | CTh_modtype (x, _modty) ->
      dleaf "CTh_modtype (%s)" x

  | CTh_module me ->
      dleaf "CTh_module (%s)" me.me_name

  | CTh_theory (x, th) ->
      dnode
        (Printf.sprintf "CTh_theory (%s)" x)
        [cth_dump th]

  | CTh_export p ->
      dleaf "CTh_export (%s)" (EcPath.tostring p)

(* -------------------------------------------------------------------- *)
let module_comps_of_module_sig_comps (comps : module_sig_body) =
  let onitem = function
    | Tys_variable (x, ty) ->
        MI_Variable {
          v_name = x;
          v_type = ty;
        }

    | Tys_function funsig ->
        MI_Function { 
          f_name = funsig.fs_name;
          f_sig  = funsig;
          f_def  = None;
        }
  in
    List.map onitem comps

(* -------------------------------------------------------------------- *)
let module_expr_of_module_sig (name : EcIdent.t) mp (tymod : module_sig) =

  let tycomps = module_comps_of_module_sig_comps tymod.mt_body in

    { me_name  = EcIdent.name name;
      me_body  = ME_Decl mp;
      me_comps = tycomps;
      me_sig   = tymod;
      me_uses  = Sp.empty;                (* FIXME *)
      me_types = [mp]; }
