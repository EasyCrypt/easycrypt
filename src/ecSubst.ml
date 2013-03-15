(* -------------------------------------------------------------------- *)
open EcUtils
open EcTypes
open EcDecl
open EcFol
open EcModules
open EcTheory

module Sp    = EcPath.Sp
module Mp    = EcPath.Mp
module Mid   = EcIdent.Mid

(* -------------------------------------------------------------------- *)
type subst_name_clash = [
  | `Ident of EcIdent.t
]

exception SubstNameClash of subst_name_clash
exception InconsistentSubst

(* -------------------------------------------------------------------- *)
type subst = {
  sb_modules : EcPath.mpath Mid.t;
  sb_path    : EcPath.path  Mp.t;
}

(* -------------------------------------------------------------------- *)
let empty : subst = {
  sb_modules = Mid.empty;
  sb_path    = Mp.empty;
}

let is_empty s = 
  Mp.is_empty s.sb_path && Mid.is_empty s.sb_modules 

let add_module (s : subst) (x : EcIdent.t) (m : EcPath.mpath) =
  let merger = function
    | None   -> Some m
    | Some _ -> raise (SubstNameClash (`Ident x))
  in
    { s with sb_modules = Mid.change merger x s.sb_modules }

let add_path (s : subst) ~src ~dst =
  assert (Mp.find_opt src s.sb_path = None);
  { s with sb_path = Mp.add src dst s.sb_path }

(* -------------------------------------------------------------------- *)
type _subst = {
  s_s   : subst;
  s_p   : (EcPath.path -> EcPath.path);
  s_fmp : (EcPath.mpath -> EcPath.mpath);
  s_ty  : (ty -> ty);
}

let _subst_of_subst s = 
  let sp = EcPath.p_subst s.sb_path in
  let sm = EcPath.Hm.memo 107 (EcPath.m_subst sp s.sb_modules) in
  let st = EcTypes.ty_subst { ty_subst_id with ts_p = sp } in
  { s_s   = s;
    s_p   = sp;
    s_fmp = sm;
    s_ty  = st; }

let e_subst_of_subst (s:_subst) = 
  { es_p   = s.s_p;
    es_ty  = s.s_ty;
    es_mp  = s.s_fmp;
    es_loc = Mid.empty; }

let f_subst_of_subst (s:_subst) = 
  { fs_p   = s.s_p;
    fs_ty  = s.s_ty;
    fs_mp  = s.s_s.sb_modules;
    fs_loc = Mid.empty;
    fs_mem = Mid.empty; }

(* -------------------------------------------------------------------- *)
let subst_variable (s : _subst) (x : variable) =
  { x with v_type = s.s_ty x.v_type; }

(* -------------------------------------------------------------------- *)
let rec subst_modsig_body_item (s : _subst) (item : module_sig_body_item) =
  match item with
  | Tys_variable vd ->
      Tys_variable (subst_variable s vd)

  | Tys_function funsig ->
      let args' = List.map (subst_variable s) (fst funsig.fs_sig) in
      let res'  = s.s_ty (snd funsig.fs_sig) in
      let uses' = funsig.fs_uses in (* FIXME *)
      Tys_function
        { fs_name = funsig.fs_name;
          fs_sig  = (args', res') ;
          fs_uses = uses'         }

(* -------------------------------------------------------------------- *)
and subst_modsig_body (s : _subst) (sbody : module_sig_body) =
  List.map (subst_modsig_body_item s) sbody

(* -------------------------------------------------------------------- *)
and subst_modsig (s : _subst) (comps : module_sig) =
  { mt_params = comps.mt_params;
    mt_body   = subst_modsig_body s comps.mt_body;
    mt_mforb  = 
      Sp.fold
        (fun p mf -> Sp.add (s.s_p p) mf)
        comps.mt_mforb Sp.empty; }

(* -------------------------------------------------------------------- *)
let subst_function_def (s : _subst) (def : function_def) =
  let es = e_subst_of_subst s in
  { f_locals = def.f_locals;
    f_body   = s_subst es def.f_body;
    f_ret    = omap def.f_ret (e_subst es); }

(* -------------------------------------------------------------------- *)
let subst_function (s : _subst) (f : function_) =
  let args' = List.map (subst_variable s) (fst f.f_sig.fs_sig) in
  let res'  = s.s_ty (snd f.f_sig.fs_sig) in
  let uses' = f.f_sig.fs_uses in (* FIXME *)
  let def'  = omap f.f_def (subst_function_def s)
      
  in
    { f_name = f.f_name;
      f_sig  = { fs_name = f.f_sig.fs_name;
                 fs_sig  = (args', res')  ;
                 fs_uses = uses'          ; };
      f_def  = def' }

(* -------------------------------------------------------------------- *)
let rec subst_module_item (s : _subst) (item : module_item) =
  match item with
  | MI_Module m ->
      let m' = subst_module s m in
      MI_Module m'

  | MI_Variable x ->
      let x' = subst_variable s x in
      MI_Variable x'

  | MI_Function f ->
      let f'     = subst_function s f in
      MI_Function f'

(* -------------------------------------------------------------------- *)
and subst_module_items (s : _subst) (items : module_item list) =
  List.map (subst_module_item s) items

(* -------------------------------------------------------------------- *)
and subst_module_struct (s : _subst) (bstruct : module_structure) =
  let sbody, newparams =
    if bstruct.ms_params = [] then s, []
    else
      let s, newparams = 
        List.map_fold
          (fun (s : subst) (a, aty) ->
            let a' = EcIdent.fresh a in
            let decl = a', EcPath.p_subst s.sb_path aty in
            add_module s a (EcPath.mident a'), decl)
          s.s_s bstruct.ms_params in
      _subst_of_subst s, newparams
  in
  sbody, { ms_params = newparams;
           ms_body   = subst_module_items sbody bstruct.ms_body; }

(* -------------------------------------------------------------------- *)
and subst_module_body (s : _subst) (body : module_body) =
  match body with
  | ME_Alias m -> s, ME_Alias (s.s_fmp m)

  | ME_Structure bstruct ->
      let s, bstruct = subst_module_struct s bstruct in
      s, ME_Structure bstruct

  | ME_Decl p ->
      s, ME_Decl (s.s_p p)

(* -------------------------------------------------------------------- *)
and subst_module_comps (s : _subst) (comps : module_comps) =
  (subst_module_items s comps : module_comps)

(* -------------------------------------------------------------------- *)
and subst_module (s : _subst) (m : module_expr) =
  let s, body'  = subst_module_body s m.me_body in
  let comps' = subst_module_comps s m.me_comps in
  let types' = List.map s.s_p m.me_types in
  { m with
    me_body  = body'   ;
    me_comps = comps'  ;
    me_uses  = Sp.empty;              (* FIXME *)
    me_types = types'  ; }

(* -------------------------------------------------------------------- *)
and subst_modtype (s : _subst) (modty : module_type) =
  s.s_p modty

(* -------------------------------------------------------------------- *)
let init_tparams (s : _subst) params params' = 
  if params = [] then s
  else
    let styv =  
      List.fold_left2 (fun m p p' -> Mid.add p (tvar p') m) 
        Mid.empty params params' in
    let sty = 
      { ty_subst_id with 
        ts_p = s.s_p;
        ts_v = styv; } in
    { s with s_ty = EcTypes.ty_subst sty } 

let subst_tydecl (s : _subst) (tyd : tydecl) =
  let params' = List.map EcIdent.fresh tyd.tyd_params in
  let body = 
    match tyd.tyd_type with
    | None    -> None 
    | Some ty ->
        let s = init_tparams s tyd.tyd_params params' in
        Some (s.s_ty ty) in
  { tyd_params = params'; tyd_type = body }

(* -------------------------------------------------------------------- *)
let subst_op_kind (s : _subst) dom (kind : operator_kind) =
  match kind with 
  | OB_oper (Some (params, body)) ->
      let s = e_subst_of_subst s in
      let s, ds = EcTypes.add_locals s (List.combine params dom) in
      let params = List.map fst ds in
      let body  = EcTypes.e_subst s body in
      OB_oper (Some (params, body)) 
  | OB_pred (Some (params, body)) ->   
      let s = f_subst_of_subst s in
      let s, ds = EcFol.add_locals s (List.combine params dom) in
      let params = List.map fst ds in
      let body  = EcFol.f_subst s body in
      OB_pred (Some (params, body)) 
  | _ -> kind

(* -------------------------------------------------------------------- *)
let subst_op (s : _subst) (op : operator) =
  let params = List.map EcIdent.fresh op.op_params in
  let sty    = init_tparams s op.op_params params in
  let dom    = List.map sty.s_ty op.op_dom in
  let codom  = sty.s_ty op.op_codom in
  let kind   = subst_op_kind sty op.op_dom (* the old one *) op.op_kind in
  { op_params = params;
    op_dom    = dom   ;
    op_codom  = codom ;
    op_kind   = kind  ; }

(* -------------------------------------------------------------------- *)
let subst_ax (s : _subst) (ax : axiom) =
  let params = List.map EcIdent.fresh ax.ax_params in
  let s      = init_tparams s ax.ax_params params in
  let spec   = 
    match ax.ax_spec with
    | None -> None
    | Some f -> 
        let s = f_subst_of_subst s in
        Some (EcFol.f_subst s f) in
  let kind   = 
    match ax.ax_kind with
    | Axiom   -> Axiom
    | Lemma _ -> Lemma None
  in
    { ax_params = params;
      ax_spec   = spec  ;
      ax_kind   = kind  ; }

(* -------------------------------------------------------------------- *)
(* SUBSTITUTION OVER THEORIES *)
let rec subst_theory_item (s : _subst) (item : theory_item) =
  match item with
  | Th_type (x, tydecl) ->
      Th_type (x, subst_tydecl s tydecl)

  | Th_operator (x, op) ->
      Th_operator (x, subst_op s op)

  | Th_axiom (x, ax) ->
      Th_axiom (x, subst_ax s ax)

  | Th_modtype (x, tymod) ->
      Th_modtype (x, subst_modsig s tymod)

  | Th_module m ->
      Th_module (subst_module s m)

  | Th_theory (x, th) ->
      Th_theory (x, subst_theory s th)

  | Th_export p -> 
      Th_export (s.s_p p)

(* -------------------------------------------------------------------- *)
and subst_theory (s : _subst) (items : theory) =
  List.map (subst_theory_item s) items 

(* -------------------------------------------------------------------- *)
and subst_ctheory_item (s : _subst) (item : ctheory_item) =
  match item with
  | CTh_type (x, ty) ->
      CTh_type (x, subst_tydecl s ty)

  | CTh_operator (x, op) ->
      CTh_operator (x, subst_op s op)

  | CTh_axiom (x, ax) ->
      CTh_axiom (x, subst_ax s ax)

  | CTh_modtype (x, modty) ->
      CTh_modtype (x, subst_modsig s modty)

  | CTh_module me ->
      CTh_module (subst_module s me)

  | CTh_theory (x, cth) ->
      CTh_theory (x, subst_ctheory s cth)

  | CTh_export p ->
      CTh_export (s.s_p p)

(* -------------------------------------------------------------------- *)
and subst_ctheory_struct (s : _subst) (th : ctheory_struct) =
  List.map (subst_ctheory_item s) th

(* -------------------------------------------------------------------- *)
and subst_ctheory_desc (s : _subst) (th : ctheory_desc) =
  match th with
  | CTh_struct th -> CTh_struct (subst_ctheory_struct s th)
  | CTh_clone  cl -> CTh_clone  (subst_ctheory_clone  s cl)

(* -------------------------------------------------------------------- *)
and subst_ctheory_clone (s : _subst) (cl : ctheory_clone) =
  { cthc_base = s.s_p cl.cthc_base;
    cthc_ext  = subst_ctheory_clone_override s cl.cthc_ext; }

(* -------------------------------------------------------------------- *)
and subst_ctheory_clone_override (s : _subst) overrides =
  let do1 (x, override) =
    let override =
      match override with
      | CTHO_Type ty -> CTHO_Type (s.s_ty ty)
    in
      (x, override)
  in
    List.map do1 overrides

(* -------------------------------------------------------------------- *)
and subst_ctheory (s : _subst) (cth : ctheory) =
  { cth_desc   = subst_ctheory_desc   s cth.cth_desc;
    cth_struct = subst_ctheory_struct s cth.cth_struct; }

(* -------------------------------------------------------------------- *)
(* -------------------------  Wrapper --------------------------------- *)
(* -------------------------------------------------------------------- *)

let subst_ax           s = subst_ax (_subst_of_subst s)
let subst_op           s = subst_op (_subst_of_subst s)
let subst_tydecl       s = subst_tydecl (_subst_of_subst s)
let subst_theory       s = subst_theory (_subst_of_subst s)
let subst_ctheory      s = subst_ctheory (_subst_of_subst s)

let subst_function     s = subst_function (_subst_of_subst s)
let subst_module       s = subst_module (_subst_of_subst s)
let subst_module_comps s = subst_module_comps (_subst_of_subst s)
let subst_modtype      s = subst_modtype (_subst_of_subst s)
let subst_modsig       s = subst_modsig (_subst_of_subst s)
let subst_modsig_body  s = subst_modsig_body (_subst_of_subst s)
