(* -------------------------------------------------------------------- *)
open EcUtils
open EcTypes
open EcDecl
open EcFol
open EcModules
open EcTheory
open EcAlgebra

module Sp    = EcPath.Sp
module Sm    = EcPath.Sm
module Sx    = EcPath.Sx
module Mx    = EcPath.Mx
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
  sb_path    : EcPath.path Mp.t;
  sb_tydef   : (EcIdent.t list * ty) Mp.t;
  sb_opdef   : (EcIdent.t list * expr) Mp.t;
}

(* -------------------------------------------------------------------- *)
let empty : subst = {
  sb_modules = Mid.empty;
  sb_path    = Mp.empty;
  sb_tydef   = Mp.empty;
  sb_opdef   = Mp.empty;
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

let add_tydef (s : subst) p (ids, ty) =
  assert (Mp.find_opt p s.sb_tydef = None);
  { s with sb_tydef = Mp.add p (ids, ty) s.sb_tydef }

let add_opdef (s : subst) p (ids, e) =
  assert (Mp.find_opt p s.sb_opdef = None);
  { s with sb_opdef = Mp.add p (ids, e) s.sb_opdef }

(* -------------------------------------------------------------------- *)
type _subst = {
  s_s   : subst;
  s_p   : (EcPath.path -> EcPath.path);
  s_fmp : (EcPath.mpath -> EcPath.mpath);
  s_sty : ty_subst;
  s_ty  : (ty -> ty);
  s_op  : (EcIdent.t list * expr) Mp.t;
}

let _subst_of_subst s = 
  let sp  = EcPath.p_subst s.sb_path in
  let sm  = EcPath.Hm.memo 107 (EcPath.m_subst sp s.sb_modules) in
  let sty = { ty_subst_id with ts_p = sp; ts_mp = sm; ts_def = s.sb_tydef; } in
  let st  = EcTypes.ty_subst sty in
    { s_s   = s;
      s_p   = sp;
      s_fmp = sm;
      s_sty = sty;
      s_ty  = st;
      s_op  = s.sb_opdef; }

let e_subst_of_subst (s:_subst) = 
  { es_freshen = true;
    es_p       = s.s_p;
    es_ty      = s.s_ty;
    es_opdef   = s.s_op;
    es_mp      = s.s_fmp;
    es_xp      = EcPath.x_subst s.s_fmp;
    es_loc     = Mid.empty; }

let f_subst_of_subst (s:_subst) = 
  Fsubst.f_subst_init true s.s_s.sb_modules s.s_sty s.s_op

(* -------------------------------------------------------------------- *)
let subst_variable (s : _subst) (x : variable) =
  { x with v_type = s.s_ty x.v_type; }

(* -------------------------------------------------------------------- *)
let subst_fun_uses (s : _subst) (u : uses) =
  let x_subst = EcPath.x_subst s.s_fmp in
  let calls  = List.map x_subst u.us_calls
  and reads  = Sx.fold (fun p m -> Sx.add (x_subst p) m) u.us_reads Sx.empty
  and writes = Sx.fold (fun p m -> Sx.add (x_subst p) m) u.us_writes Sx.empty in

    { us_calls = calls; us_reads = reads; us_writes = writes; }

(* -------------------------------------------------------------------- *)
let subst_oracle_info (s:_subst) (x:oracle_info) = 
  let x_subst = EcPath.x_subst s.s_fmp in
    { oi_calls  = List.map x_subst x.oi_calls;
      oi_in     = x.oi_in;
    }

(* -------------------------------------------------------------------- *)
let subst_funsig (s : _subst) (funsig : funsig) =
  let fs_params = List.map (subst_variable s) (funsig.fs_params) in
  let fs_ret    = s.s_ty (funsig.fs_ret) in

  { fs_name   = funsig.fs_name;
    fs_params = fs_params;
    fs_ret    = fs_ret; }

(* -------------------------------------------------------------------- *)
let rec subst_modsig_body_item (s : _subst) (item : module_sig_body_item) =
  match item with
  | Tys_function (funsig, oi) ->
      Tys_function (subst_funsig s funsig, subst_oracle_info s oi)

(* -------------------------------------------------------------------- *)
and subst_modsig_body (s : _subst) (sbody : module_sig_body) =
  List.map (subst_modsig_body_item s) sbody

(* -------------------------------------------------------------------- *)
and subst_modsig ?params (s : _subst) (comps : module_sig) =
  let sbody, newparams =
    match params with
    | None -> begin
        match comps.mis_params with
        | [] -> (s, [])
        | _  ->
          let aout =
            List.map_fold
              (fun (s : subst) (a, aty) ->
                let a'   = EcIdent.fresh a in
                let decl = (a', subst_modtype (_subst_of_subst s) aty) in
                  add_module s a (EcPath.mident a'), decl)
              s.s_s comps.mis_params
          in
            fst_map _subst_of_subst aout
    end

  | Some params ->
      let aout =
        List.map_fold
          (fun (s : subst) ((a, aty), a') ->
              let decl = (a', subst_modtype (_subst_of_subst s) aty) in
                add_module s a (EcPath.mident a'), decl)
            s.s_s (List.combine comps.mis_params params)
        in
          fst_map _subst_of_subst aout
  in

  let comps =
    { mis_params = newparams;
      mis_body   = subst_modsig_body sbody comps.mis_body; }
  in
    (sbody, comps)

(* -------------------------------------------------------------------- *)
and subst_modtype (s : _subst) (modty : module_type) =
  { mt_params = List.map (snd_map (subst_modtype s)) modty.mt_params;
    mt_name   = s.s_p modty.mt_name;
    mt_args   = List.map s.s_fmp modty.mt_args; }

(* -------------------------------------------------------------------- *)
let subst_function_def (s : _subst) (def : function_def) =
  let es = e_subst_of_subst s in
  { f_locals = List.map (subst_variable s) def.f_locals;
    f_body   = s_subst es def.f_body;
    f_ret    =  def.f_ret |> omap (e_subst es);
    f_uses   = subst_fun_uses s def.f_uses; }

(* -------------------------------------------------------------------- *)
let subst_function (s : _subst) (f : function_) =
  let sig' = subst_funsig s f.f_sig in
  let def' = 
    match f.f_def with 
    | FBdef def -> FBdef (subst_function_def s def)
    | FBabs oi  -> FBabs (subst_oracle_info s oi) in
  { f_name = f.f_name;
    f_sig  = sig';
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
    { ms_body   = subst_module_items s bstruct.ms_body; }

(* -------------------------------------------------------------------- *)
and subst_module_body (s : _subst) (body : module_body) =
  match body with
  | ME_Alias m ->
      ME_Alias (s.s_fmp m)

  | ME_Structure bstruct ->
      ME_Structure (subst_module_struct s bstruct)

  | ME_Decl (p, (rx,r)) -> 
    let rx = 
      EcPath.Sx.fold
        (fun x r -> EcPath.Sx.add (EcPath.x_subst s.s_fmp x) r) rx EcPath.Sx.empty in
    let r = 
      EcPath.Sm.fold 
        (fun x r -> EcPath.Sm.add (s.s_fmp x) r) r EcPath.Sm.empty
      in
        ME_Decl (subst_modtype s p, (rx, r))

(* -------------------------------------------------------------------- *)
and subst_module_comps (s : _subst) (comps : module_comps) =
  (subst_module_items s comps : module_comps)

(* -------------------------------------------------------------------- *)
and subst_module (s : _subst) (m : module_expr) =
  let s, me_sig = subst_modsig s m.me_sig in
  let me_body   = subst_module_body s m.me_body in
  let me_comps  = subst_module_comps s m.me_comps in
    { m with me_body; me_comps; me_sig; }

(* -------------------------------------------------------------------- *)
let init_tparams (s : _subst) (params : ty_params) (params' : ty_params) =
  if params = [] then s
  else
    let styv =  
      List.fold_left2 (fun m (p, _) (p', _) -> Mid.add p (tvar p') m) 
        Mid.empty params params' in
    let sty = 
      { ty_subst_id with 
          ts_def = s.s_sty.ts_def;
          ts_p   = s.s_p;
          ts_mp  = s.s_fmp;
          ts_v   = Mid.find_opt^~ styv; }
    in
      { s with s_sty = sty; s_ty = EcTypes.ty_subst sty } 

let subst_typaram (s : _subst) ((id, tc) : ty_param) =
  (EcIdent.fresh id,
   Sp.fold (fun p tc -> Sp.add (s.s_p p) tc) tc Sp.empty)

let subst_tydecl (s : _subst) (tyd : tydecl) =
  let params' = List.map (subst_typaram s) tyd.tyd_params in
  let body = 
    match tyd.tyd_type with
    | `Abstract tc ->
        `Abstract (Sp.fold (fun p tc -> Sp.add (s.s_p p) tc) tc Sp.empty)
    | `Concrete ty ->
        let s = init_tparams s tyd.tyd_params params' in
          `Concrete (s.s_ty ty)
  in
    { tyd_params = params'; tyd_type = body }

(* -------------------------------------------------------------------- *)
let subst_op_kind (s : _subst) (kind : operator_kind) =
  match kind with 
  | OB_oper (Some body) ->
      let s = e_subst_of_subst s in
      let body  = EcTypes.e_subst s body in
        OB_oper (Some body)

  | OB_pred (Some body) ->   
      let s = f_subst_of_subst s in
      let body  = Fsubst.f_subst s body in
        OB_pred (Some body) 

  | OB_oper None | OB_pred None -> kind

(* -------------------------------------------------------------------- *)
let subst_op (s : _subst) (op : operator) =
  let tparams = List.map (subst_typaram s) op.op_tparams in
  let sty     = init_tparams s op.op_tparams tparams in
  let ty      = sty.s_ty op.op_ty in
  let kind    = subst_op_kind sty op.op_kind in
    { op_tparams = tparams;
      op_ty      = ty     ;
      op_kind    = kind   ; }

(* -------------------------------------------------------------------- *)
let subst_ax (s : _subst) (ax : axiom) =
  let params = List.map (subst_typaram s) ax.ax_tparams in
  let s      = init_tparams s ax.ax_tparams params in
  let spec   = 
    match ax.ax_spec with
    | None -> None
    | Some f -> 
        let s = f_subst_of_subst s in
          Some (Fsubst.f_subst s f)
  in
     { ax_tparams = params;
       ax_spec    = spec;
       ax_kind    = ax.ax_kind;
       ax_nosmt   = ax.ax_nosmt; }

(* -------------------------------------------------------------------- *)
let subst_ring (s : _subst) cr =
  { r_type  = s.s_ty cr.r_type;
    r_zero  = s.s_p cr.r_zero;
    r_one   = s.s_p cr.r_one;
    r_add   = s.s_p cr.r_add;
    r_opp   = s.s_p cr.r_opp;
    r_mul   = s.s_p cr.r_mul;
    r_exp   = s.s_p cr.r_exp;
    r_sub   = cr.r_sub |> omap s.s_p;
    r_embed =
      match cr.r_embed with
      | `Direct  -> `Direct
      | `Embed p -> `Embed (s.s_p p); }

let subst_field (s : _subst) cr =
  { f_ring = subst_ring s cr.f_ring;
    f_inv  = s.s_p cr.f_inv;
    f_div  = cr.f_div |> omap s.s_p; }

(* -------------------------------------------------------------------- *)
let subst_instance (s : _subst) tci =
  match tci with
  | `Ring    cr -> `Ring  (subst_ring  s cr)
  | `Field   cr -> `Field (subst_field s cr)
  | `General p  -> `General (s.s_p p)

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
      Th_modtype (x, snd (subst_modsig s tymod))

  | Th_module m ->
      Th_module (subst_module s m)

  | Th_theory (x, th) ->
      Th_theory (x, subst_theory s th)

  | Th_export p -> 
      Th_export (s.s_p p)

  | Th_instance (p, tci) ->
      Th_instance (s.s_p p, subst_instance s tci)

  | Th_typeclass (x : EcSymbols.symbol) ->
      Th_typeclass x

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
      CTh_modtype (x, snd (subst_modsig s modty))

  | CTh_module me ->
      CTh_module (subst_module s me)

  | CTh_theory (x, cth) ->
      CTh_theory (x, subst_ctheory s cth)

  | CTh_export p ->
      CTh_export (s.s_p p)

  | CTh_instance (p, cr) ->
      CTh_instance (s.s_p p, subst_instance s cr)

  | CTh_typeclass x ->
      CTh_typeclass x

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
let subst_modsig         = fun ?params s x -> snd (subst_modsig ?params (_subst_of_subst s) x)
let subst_modsig_body  s = subst_modsig_body (_subst_of_subst s)

let subst_mpath        s = (_subst_of_subst s).s_fmp
let subst_path         s = (_subst_of_subst s).s_p

let subst_form         s = fun f -> (Fsubst.f_subst (f_subst_of_subst (_subst_of_subst s)) f)
