(* -------------------------------------------------------------------- *)
open EcUtils
open EcTypes
open EcDecl
open EcFol
open EcTypesmod
open EcTypestheo

module Sp    = EcPath.Sp
module Mid   = EcIdent.Mid

(* -------------------------------------------------------------------- *)
type subst_name_clash = [
  | `Ident of EcIdent.t
]

exception SubstNameClash of subst_name_clash
exception InconsistentSubst

(* -------------------------------------------------------------------- *)
type subst = {
  sb_locals  : EcIdent.t   Mid.t;
  sb_modules : EcPath.mpath Mid.t;
}

(* -------------------------------------------------------------------- *)
let empty : subst = {
  sb_locals  = Mid.empty;
  sb_modules = Mid.empty;
}

let is_empty s = 
  Mid.is_empty s.sb_locals && Mid.is_empty s.sb_modules 

let add_module (s : subst) (x : EcIdent.t) (m : EcPath.mpath) =
  let merger = function
    | None   -> Some m
    | Some _ -> raise (SubstNameClash (`Ident x))
  in
    { s with sb_modules = Mid.change merger x s.sb_modules }

let add_local (s : subst) (x : EcIdent.t) (x' : EcIdent.t) =
  let merger = function
    | None   -> Some x'
    | Some _ ->raise (SubstNameClash (`Ident x))
  in
    { s with sb_locals = Mid.change merger x s.sb_locals }

let add_locals subst bindings =
  List.fold_left
    (fun s (x, x') -> add_local s x x')
    subst bindings

(* -------------------------------------------------------------------- *)
let subst_path  (_s : subst) (p : EcPath.path) = p
let subst_local (_s : subst) (x : EcIdent.t)   = x

let rec subst_mpath (s : subst) (m : EcPath.mpath) = 
  let p,args = m.EcPath.m_node in
  let args = List.map (List.map (subst_mpath s)) args in
  let rec aux p args = 
    match p.EcPath.p_node, args with
    | EcPath.Psymbol _, _ -> raise Not_found 
    | EcPath.Pident id, [a] ->
        let m = Mid.find id s.sb_modules in
        assert (a = []); (* FIXME *)
        m
    | EcPath.Pqname(p,id), a::args ->
        EcPath.mqname (aux p args) id a 
    | _, _ -> assert false in
  try aux p args with Not_found -> EcPath.mpath p args

(* -------------------------------------------------------------------- *)
let rec subst_ty (s : subst) (ty : ty) =
  match ty.ty_node with
  | Tunivar _ -> assert false

  | Tvar x -> tvar (subst_local s x)

  | Ttuple tys ->
      let tys = List.map (subst_ty s) tys in
      ttuple tys

  | Tconstr (p, tys) ->
      let p   = subst_path s p in
      let tys = List.map (subst_ty s) tys in
      tconstr p tys

  | Tfun (t1,t2) -> tfun (subst_ty s t1) (subst_ty s t2)

(* -------------------------------------------------------------------- *)
let subst_lpattern (s : subst) (p : lpattern) =
  match p with
  | LSymbol x ->
      let x' = EcIdent.fresh x in
      (add_local s x x', LSymbol x')

  | LTuple xs ->
      let xs' = List.map EcIdent.fresh xs in
      let s'  = add_locals s (List.combine xs xs') in
      (s', LTuple xs')

(* -------------------------------------------------------------------- *)
let subst_pvar s x =
  { x with pv_name = subst_mpath s x.pv_name } 
  
let rec subst_tyexpr (s : subst) (e : tyexpr) =
  match e.tye_desc with
  | Eint i ->
      e_int i

  | Elocal x ->
      let x  = subst_local s x in
      e_local x

  | Evar x ->
      e_var (subst_pvar s x)

  | Eop(p, tys) ->
      e_op (subst_path s p) (List.map (subst_ty s) tys)

  | Eapp (e, es) ->
      e_app (subst_tyexpr s e) (List.map (subst_tyexpr s) es)

  | Elet (p, e1, e2) ->
      let (sbody, p) = subst_lpattern s p in
      let e1 = subst_tyexpr s     e1 in
      let e2 = subst_tyexpr sbody e2 in
        e_let p e1 e2

  | Etuple es ->
      let es = List.map (subst_tyexpr s) es in
        e_tuple es

  | Eif (c, e1, e2) ->
      let c  = subst_tyexpr s c in
      let e1 = subst_tyexpr s e1 in
      let e2 = subst_tyexpr s e2 in
        e_if c e1 e2










(* SUBSTITUTION OVER MODULES *)


(* -------------------------------------------------------------------- *)
let rec subst_modsig_body_item (s : subst) (item : module_sig_body_item) =
  match item with
  | Tys_variable (x, ty) ->
      let ty' = subst_ty s ty in
        Tys_variable (x, ty')

  | Tys_function funsig ->
      let args' = List.map
                    (fun (x, ty) -> (x, subst_ty s ty))
                    (fst funsig.fs_sig) in
      let res'  = subst_ty s (snd funsig.fs_sig) in
      let uses' = funsig.fs_uses in

        Tys_function
          { fs_name = funsig.fs_name;
            fs_sig  = (args', res') ;
            fs_uses = uses'         }

(* -------------------------------------------------------------------- *)
and subst_modsig_body (s : subst) (sbody : module_sig_body) =
  List.map (subst_modsig_body_item s) sbody

(* -------------------------------------------------------------------- *)
and subst_modsig (s : subst) (comps : module_sig) =
  { mt_params = comps.mt_params;
    mt_body   = subst_modsig_body s comps.mt_body;
    mt_mforb  = 
      Sp.fold
        (fun p mf -> Sp.add (subst_path s p) mf)
        comps.mt_mforb Sp.empty; }

(* -------------------------------------------------------------------- *)
let rec subst_stmt (s : subst) (stmt : stmt) =
  List.map (subst_instr s) stmt

(* -------------------------------------------------------------------- *)
and subst_instr (s : subst) (instr : instr) =
  match instr with
  | Sasgn (lv, e) ->
      let lv = subst_lvalue s lv in
      let e  = subst_tyexpr s e  in
      Sasgn (lv, e)
  | Srnd (lv, e) ->
      let lv = subst_lvalue s lv in
      let e  = subst_tyexpr s e  in
      Srnd (lv, e)

  | Scall (lv, p, es) ->
      let lv = omap lv (subst_lvalue s) in
      let p  = subst_mpath s p in
      let es = List.map (subst_tyexpr s) es in
        Scall (lv, p, es)

  | Sif (e, s1, s2) ->
      let e  = subst_tyexpr s e  in
      let s1 = subst_stmt   s s1 in
      let s2 = subst_stmt   s s2 in
        Sif (e, s1, s2)

  | Swhile (e, st) ->
      let e  = subst_tyexpr s e  in
      let st = subst_stmt   s st in
        Swhile (e, st)

  | Sassert e ->
      Sassert (subst_tyexpr s e)

(* -------------------------------------------------------------------- *)
and subst_lvalue (s : subst) (lvalue : lvalue) =
  match lvalue with
  | LvVar (p, ty) ->
      LvVar (subst_pvar s p, subst_ty s ty)

  | LvTuple ptys ->
      let ptys = List.map (fun (p, ty) -> subst_pvar s p, subst_ty s ty) ptys in
      LvTuple ptys

  | LvMap ((p1,tys), p2, e, ty) ->
      let p1 = subst_path   s p1 in
      let tys = List.map (subst_ty s) tys in
      let p2 = subst_pvar     s p2 in
      let e  = subst_tyexpr s e  in
      let ty = subst_ty     s ty in
      LvMap ((p1,tys), p2, e, ty)

(* -------------------------------------------------------------------- *)
let subst_variable (s : subst) (x : variable) =
  { x with v_type = subst_ty s x.v_type; }

(* -------------------------------------------------------------------- *)
let rec subst_function (s : subst) (f : function_) =
  let args'   = List.map
                  (fun (x, ty) -> (x, subst_ty s ty))
                  (fst f.f_sig.fs_sig) in
  let res'    = subst_ty s (snd f.f_sig.fs_sig) in
  let uses'   = f.f_sig.fs_uses in
  let def'    = omap f.f_def (subst_function_def s)
      
  in

    { f_name = f.f_name;
      f_sig  = { fs_name = f.f_sig.fs_name;
                 fs_sig  = (args', res')  ;
                 fs_uses = uses'          ; };
      f_def  = def' }

(* -------------------------------------------------------------------- *)
and subst_function_def (s : subst) (def : function_def) =
  { f_locals = def.f_locals;
    f_body   = subst_stmt s def.f_body;
    f_ret    = omap def.f_ret (subst_tyexpr s); }

(* -------------------------------------------------------------------- *)
let rec subst_module_item (s : subst) (item : module_item) =
  match item with
  | MI_Module m ->
      let m' = subst_module s m in

        (s, MI_Module m')

  | MI_Variable x ->
      let x' = subst_variable s x in

        (s, MI_Variable x')

  | MI_Function f ->
      let f'     = subst_function s f in

        (s, MI_Function f')

(* -------------------------------------------------------------------- *)
and subst_module_items (s : subst) (items : module_item list) =
  let _, items =
    List.map_fold
      (fun (s : subst) item ->
        subst_module_item s item)
      s items
  in
    items

(* -------------------------------------------------------------------- *)
and subst_module_struct (s : subst) (bstruct : module_structure) =
  let sbody, newparams =
    List.map_fold
      (fun (s : subst) (a, aty) ->
        let a' = EcIdent.fresh a in
          (add_module s a (EcPath.mident a'), (a', subst_path s aty)))
      s bstruct.ms_params
  in
    { ms_params = newparams;
      ms_body   = subst_module_items sbody bstruct.ms_body; }

(* -------------------------------------------------------------------- *)
and subst_module_body (s : subst) (body : module_body) =
  match body with
  | ME_Alias m -> ME_Alias (subst_mpath s m)

  | ME_Structure bstruct ->
      ME_Structure (subst_module_struct s bstruct)

  | ME_Decl p ->
      ME_Decl (subst_path s p)

(* -------------------------------------------------------------------- *)
and subst_module_comps (_s : subst) (_comps : module_comps) =
  []                                    (* FIXME *)

(* -------------------------------------------------------------------- *)
and subst_module (s : subst) (m : module_expr) =
  let body'  = subst_module_body s m.me_body in
  let comps' = subst_module_comps s m.me_comps in
  let types' = List.map (subst_path s) m.me_types in

    { m with
        me_body  = body'   ;
        me_comps = comps'  ;
        me_uses  = Sp.empty;              (* FIXME *)
        me_types = types'  ; }













(* SUBSTITUTION OVER FORMULAE *)


(* -------------------------------------------------------------------- *)
let rec subst_form (s : subst) (f : form) =
  let f_node = subst_form_node s f.f_node
  and f_ty   = subst_ty s f.f_ty
  in mk_form f_node f_ty

and subst_form_node (s : subst) (f : f_node) =
  match f with
  | Fint _ -> f

  | Fquant (mode, bindings, f) ->
      let newbindings =
        List.map
          (fun (x, ty) -> (EcIdent.fresh x, subst_ty s ty))
          bindings in

      let sbody =
        add_locals s
          (List.combine
             (List.map (EcIdent.fresh -| fst) bindings   )
             (List.map (EcIdent.fresh -| fst) newbindings))
      in

        Fquant (mode, newbindings, subst_form sbody f)

  | Flet (p, f1, f2) ->
      let (sbody, p) = subst_lpattern s p in
      let f1 = subst_form s     f1 in
      let f2 = subst_form sbody f2 in
        Flet (p, f1, f2)

  | Fif (c, f1, f2) ->
      let c  = subst_form s c  in
      let f1 = subst_form s f1 in
      let f2 = subst_form s f2 in
        Fif (c, f1, f2)

  | Flocal x ->
      Flocal (subst_local s x)

  | Fpvar (x, side) ->
      let x  = subst_pvar s x in
      Fpvar (x, side)

  | Fop(p,tys) -> Fop(subst_path s p, List.map (subst_ty s) tys)

  | Fapp (f, fs) ->
      let f = subst_form s f in
      let fs = List.map (subst_form s) fs in
      Fapp (f, fs)

  | Ftuple fs ->
      Ftuple (List.map (subst_form s) fs)

  | Fhoare ( pre, body, post) ->
    Fhoare (subst_form s pre, subst_function_def s body, subst_form s post)

(* -------------------------------------------------------------------- *)
let subst_tydecl (s : subst) (tyd : tydecl) =
  let params = List.map EcIdent.fresh tyd.tyd_params in
    match tyd.tyd_type with
    | None    -> { tyd_params = params; tyd_type = None; }
    | Some ty ->
        let s = add_locals s (List.combine tyd.tyd_params params) in
          { tyd_params = params;
            tyd_type   = Some (subst_ty s ty); }

(* -------------------------------------------------------------------- *)
let subst_op_kind (s : subst) (kind : operator_kind) =
  let locals =
    match kind with
    | OB_oper i -> odfl [] (omap i fst)
    | OB_pred i -> odfl [] (omap i fst) in

  let newlocals = List.map EcIdent.fresh locals in
  let sdef = add_locals s (List.combine locals newlocals) in

    match kind with
    | OB_oper i ->
      let def = omap i (fun (_, e) -> (newlocals, subst_tyexpr sdef e)) in
      OB_oper def

    | OB_pred i ->
      let def = omap i (fun (_, e) -> (newlocals, subst_form sdef e)) in
      OB_pred def

(* -------------------------------------------------------------------- *)
let subst_op (s : subst) (op : operator) =
  let params = List.map EcIdent.fresh op.op_params in
  let sty    = add_locals s (List.combine op.op_params params) in
  let dom    = List.map (subst_ty sty) op.op_dom in
  let codom  = subst_ty sty op.op_codom in
  let kind   = subst_op_kind sty op.op_kind in

    { op_params = params;
      op_dom    = dom   ;
      op_codom  = codom ;
      op_kind   = kind  ; }

(* -------------------------------------------------------------------- *)
let subst_ax (s : subst) (ax : axiom) =
  let params = List.map EcIdent.fresh ax.ax_params in
  let sty    = add_locals s (List.combine ax.ax_params params) in
  let spec   = omap ax.ax_spec (subst_form sty) in 
  let kind   = 

    match ax.ax_kind with
    | Axiom   -> Axiom
    | Lemma _ -> Lemma None

  in
    { ax_params = params;
      ax_spec   = spec  ;
      ax_kind   = kind  ; }








(* SUBSTITUTION OVER THEORIES *)

(* -------------------------------------------------------------------- *)
let rec subst_theory_item (s : subst) (item : theory_item) =
  match item with
  | Th_type (x, tydecl) ->
      (s, Th_type (x, subst_tydecl s tydecl))

  | Th_operator (x, op) ->
      (s, Th_operator (x, subst_op s op))

  | Th_axiom (x, ax) ->
      (s, Th_axiom (x, subst_ax s ax))

  | Th_modtype (x, tymod) ->
      (s, Th_modtype (x, subst_modsig s tymod))

  | Th_module m ->
      (s, Th_module (subst_module s m))

  | Th_theory (x, th) ->
      let th' = subst_theory s th in
        (s, Th_theory (x, th'))

  | Th_export p -> (s, Th_export (subst_path s p))

(* -------------------------------------------------------------------- *)
and subst_theory (s : subst) (items : theory) =
  let _, items =
    List.fold_left
      (fun (s, acc) item ->
        let (s, item) = subst_theory_item s item in
          (s, item :: acc))
      (s, []) items
  in
    List.rev items

(* -------------------------------------------------------------------- *)
let subst_modtype (s : subst) (modty : module_type) =
  subst_path s modty
