(* -------------------------------------------------------------------- *)
open EcUtils
open EcTypes
open EcDecl
open EcFol
open EcTypesmod

module Sp = EcPath.Sp

(* -------------------------------------------------------------------- *)
type subst1 = [
  | `Path  of EcPath.path
  | `Local of EcIdent.t
]

type subst = subst1 EcIdent.Mid.t

exception SubstNameClash of EcIdent.t
exception InconsistentSubst

(* -------------------------------------------------------------------- *)
let empty : subst = EcIdent.Mid.empty

let add (s : subst) (x : EcIdent.t) (s1 : subst1) : subst =
  let merger = function
    | None   -> Some s1
    | Some _ -> raise (SubstNameClash x)
  in
    EcIdent.Mid.change merger x s

let add_locals (s : subst) (locals : (EcIdent.t * EcIdent.t) list) : subst =
  List.fold_left (fun s (x, x') -> add s x (`Local x')) s locals

let create (sb1 : (EcIdent.t * subst1) list) : subst =
  List.fold_left (fun s (x, s1) -> add s x s1) empty sb1

let compose (s1 : subst) (s2 : subst) : subst =
  EcIdent.Mid.union
    (fun x _ _ -> raise (SubstNameClash x))
    s1 s2

(* -------------------------------------------------------------------- *)
let subst_path (s : subst) (p : EcPath.path) =
  match EcIdent.Mid.find_opt (EcPath.basename p) s with
  | None           -> p
  | Some (`Path p) -> p
  | Some _         -> raise InconsistentSubst

let subst_local (s : subst) (x : EcIdent.t) =
  match EcIdent.Mid.find_opt x s with
  | None            -> x
  | Some (`Local x) -> x
  | Some _          -> raise InconsistentSubst

(* -------------------------------------------------------------------- *)
let rec subst_ty (s : subst) (ty : ty) =
  match ty with
  | Tunivar _ -> assert false

  | Tvar x -> Tvar (subst_local s x)

  | Ttuple tys ->
      let tys = List.map (subst_ty s) tys in
        Ttuple tys

  | Tconstr (p, tys) ->
      let p   = subst_path s p in
      let tys = List.map (subst_ty s) tys in
        Tconstr (p, tys)

(* -------------------------------------------------------------------- *)
let subst_lpattern (s : subst) (p : lpattern) =
  match p with
  | LSymbol x ->
      let x' = EcIdent.fresh x in
        (add s x (`Local x'), LSymbol x')

  | LTuple xs ->
      let xs' = List.map EcIdent.fresh xs in
      let s'  = add_locals s (List.combine xs xs') in
        (s', LTuple xs')

(* -------------------------------------------------------------------- *)
let rec subst_tyexpr (s : subst) (e : tyexpr) =
  match e.tye_desc with
  | Eint i ->
      e_int i

  | Eflip  ->
      e_flip ()

  | Einter (e1, e2) ->
      let e1 = subst_tyexpr s e1 in
      let e2 = subst_tyexpr s e2 in
        e_inter e1 e2

  | Ebitstr e ->
      let e = subst_tyexpr s e in
        e_bitstr e

  | Eexcepted (e1, e2) ->
      let e1 = subst_tyexpr s e1 in
      let e2 = subst_tyexpr s e2 in
        e_excepted e1 e2

  | Elocal (x, ty) ->
      let x  = subst_local s x in
      let ty = subst_ty s ty in
        e_local x ty

  | Evar (x, ty) ->
      let x  = { x with pv_name = subst_path s x.pv_name } in
      let ty = subst_ty s ty in
        e_var x ty

  | Eapp (p, es, ty) ->
      let p   = subst_path s p in
      let tys = List.map (subst_tyexpr s) es in
      let ty  = subst_ty s ty in
        e_app p tys ty

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

(* -------------------------------------------------------------------- *)
let rec subst_form (s : subst) (f : form) =
  let f_node = subst_form_node s f.f_node
  and f_ty   = subst_ty s f.f_ty
  and f_fv   = EcIdent.Mid.empty        (* FIXME *)
  in
    { f_node = f_node; f_ty = f_ty; f_fv = f_fv }

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

  | Fpvar (x, ty, side) ->
      let x  = { x with pv_name = subst_path s x.pv_name } in
      let ty = subst_ty s ty in
        Fpvar (x, ty, side)

  | Fapp (p, fs) ->
      let p  = subst_path s p in
      let fs = List.map (subst_form s) fs in
        Fapp (p, fs)

  | Ftuple fs ->
      Ftuple (List.map (subst_form s) fs)

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
    | OB_oper i -> odfl [] (omap i.op_def fst)
    | OB_pred i -> odfl [] (omap i.op_def fst)
    | OB_prob i -> odfl [] (omap i.op_def fst) in

  let newlocals = List.map EcIdent.fresh locals in
  let sdef = add_locals s (List.combine locals newlocals) in

    match kind with
    | OB_oper i ->
      let def = omap i.op_def
        (fun (_, e) -> (newlocals, subst_tyexpr sdef e))
      in
        OB_oper { op_def = def; op_info = (); }

    | OB_pred i ->
      let def = omap i.op_def
        (fun (_, e) -> (newlocals, subst_form sdef e))
      in
        OB_pred { op_def = def; op_info = (); }

    | OB_prob i ->
      let def = omap i.op_def
        (fun (_, e) -> (newlocals, subst_tyexpr sdef e))
      in
        OB_prob { op_def = def; op_info = (); }

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

(* -------------------------------------------------------------------- *)
let subst_tysig_item (s : subst) (item : tysig_item) =
  match item with
  | Tys_variable (x, ty) ->
      let ty' = subst_ty s ty in
        Tys_variable (x, ty')

  | Tys_function funsig ->
      let args' = List.map
                    (fun (x, ty) -> (EcIdent.fresh x, subst_ty s ty))
                    (fst funsig.fs_sig) in
      let res'  = subst_ty s (snd funsig.fs_sig) in
      let uses' = funsig.fs_uses in

        Tys_function
          { fs_name = funsig.fs_name;
            fs_sig  = (args', res') ;
            fs_uses = uses'         }

(* -------------------------------------------------------------------- *)
let subst_tysig (s : subst) (tysig : tysig) =
  List.map (subst_tysig_item s) tysig

(* -------------------------------------------------------------------- *)
let rec subst_modtype (s : subst) (tymod : tymod) =
    let newparams =
      List.map
        (fun (a, aty) ->
          (EcIdent.fresh a, subst_modtype s aty))
        tymod.tym_params in

    let ssig = add_locals s
      (List.combine
         (List.map fst tymod.tym_params)
         (List.map fst newparams))
    in
      { tym_params = newparams;
        tym_sig    = subst_tysig ssig tymod.tym_sig;
        tym_mforb  = 
          Sp.fold
            (fun p mf -> Sp.add (subst_path s p) mf)
            tymod.tym_mforb Sp.empty; }

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

  | Scall (lv, p, es) ->
      let lv = omap lv (subst_lvalue s) in
      let p  = subst_path s p in
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
      let p  = subst_path s p  in
      let ty = subst_ty   s ty in
        LvVar (p, ty)

  | LvTuple ptys ->
      let ptys = List.map
        (fun (p, ty) ->
          let p  = subst_path s p  in
          let ty = subst_ty   s ty in
            (p, ty))
        ptys
      in
        LvTuple ptys

  | LvMap (p1, p2, e, ty) ->
      let p1 = subst_path   s p1 in
      let p2 = subst_path   s p2 in
      let e  = subst_tyexpr s e  in
      let ty = subst_ty     s ty in
        LvMap (p1, p2, e, ty)

(* -------------------------------------------------------------------- *)
let subst_variable (s : subst) (x : variable) =
  { v_name = EcIdent.fresh x.v_name;
    v_type = subst_ty s x.v_type; }

(* -------------------------------------------------------------------- *)
let subst_function (s : subst) (f : function_) =
  let args'   = List.map
                  (fun (x, ty) -> (EcIdent.fresh x, subst_ty s ty))
                  (fst f.f_sig.fs_sig) in
  let res'    = subst_ty s (snd f.f_sig.fs_sig) in
  let uses'   = f.f_sig.fs_uses in
  let locals' = List.map
                  (fun (x, ty) -> (EcIdent.fresh x, subst_ty s ty))
                  f.f_locals in

  let sbody = s in
  let sbody = add_locals sbody
                (List.map_combine fst fst (fst f.f_sig.fs_sig) args') in
  let sbody = add_locals sbody
                (List.map_combine fst fst f.f_locals locals') in

  let body' = subst_stmt sbody f.f_body in
  let ret'  = omap f.f_ret (subst_tyexpr sbody) in

    { f_name = EcIdent.fresh f.f_name;
      f_sig  = { fs_name = f.f_sig.fs_name;
                 fs_sig  = (args', res')  ;
                 fs_uses = uses'          ; };

      f_locals = locals';
      f_body   = body'  ;
      f_ret    = ret'   ;
    }

(* -------------------------------------------------------------------- *)
let rec subst_module_item (s : subst) (scope : EcPath.path) (item : module_item) =
  match item with
  | MI_Module m ->
      let m'     = subst_module s scope m in
      let scope' = EcPath.Pqname (scope, m'.me_name) in
      let s'     = add s m.me_name (`Path scope') in

        (s', MI_Module m')

  | MI_Variable x ->
      let x'     = subst_variable s x in
      let scope' = EcPath.Pqname (scope, x'.v_name) in
      let s'     = add s x.v_name (`Path scope') in

        (s', MI_Variable x')

  | MI_Function f ->
      let f'     = subst_function s f in
      let scope' = EcPath.Pqname (scope, f'.f_name) in
      let s'     = add s f'.f_name (`Path scope') in
        (s', MI_Function f')

(* -------------------------------------------------------------------- *)
and subst_module_items (s : subst) (scope : EcPath.path) (items : module_item list) =
  let _, items =
    List.map_fold
      (fun (s : subst) item ->
        subst_module_item s scope item)
      s items
  in
    items

(* -------------------------------------------------------------------- *)
and subst_module_struct (s : subst) (scope : EcPath.path) (bstruct : module_structure) =
  let sbody, newparams =
    List.map_fold
      (fun (s : subst) (a, aty) ->
        let a' = EcIdent.fresh a in
          (add s a (`Local a'), (a', subst_modtype s aty)))
      s bstruct.ms_params
  in
    { ms_params = newparams;
      ms_body   = subst_module_items sbody scope bstruct.ms_body; }

(* -------------------------------------------------------------------- *)
and subst_module_body (s : subst) (scope : EcPath.path) (body : module_body) =
  match body with
  | ME_Ident p -> ME_Ident (subst_path s p)

  | ME_Application (p, args) ->
      ME_Application (subst_path s p, List.map (subst_path s) args)

  | ME_Structure bstruct ->
      ME_Structure (subst_module_struct s scope bstruct)

  | ME_Decl p ->
      ME_Decl (subst_path s p)

(* -------------------------------------------------------------------- *)
and subst_module (s : subst) (scope : EcPath.path) (m : module_expr) =
  let name'  = EcIdent.fresh m.me_name in
  let scope' = EcPath.Pqname (scope, name') in
  let sbody  = add s m.me_name (`Path scope') in
  let body'  = subst_module_body sbody scope' m.me_body in
  let tysig' = subst_modtype s m.me_sig in

    { me_name = name' ;
      me_body = body' ;
      me_meta = None  ;           (* FIXME *)
      me_sig  = tysig'; }

(* -------------------------------------------------------------------- *)
let rec subst_theory_item (s : subst) (scope : EcPath.path) (item : theory_item) =
  match item with
  | Th_type (x, tydecl) ->
      let x' = EcIdent.fresh x in
      let s' = add s x (`Path (EcPath.Pqname (scope, x'))) in
        (s', Th_type (x', subst_tydecl s' tydecl))

  | Th_operator (x, op) ->
      let x' = EcIdent.fresh x in
      let s' = add s x (`Path (EcPath.Pqname (scope, x'))) in
        (s', Th_operator (x', subst_op s op))

  | Th_axiom (x, ax) ->
      let x'  = EcIdent.fresh x in
      let s'  = add s x (`Path (EcPath.Pqname (scope, x'))) in
      (s', Th_axiom (x', subst_ax s ax))

  | Th_modtype (x, tymod) ->
      let x' = EcIdent.fresh x in
      let s' = add s x (`Path (EcPath.Pqname (scope, x'))) in
        (s', Th_modtype (x', subst_modtype s tymod))

  | Th_module m ->
      let m' = subst_module s scope m in
      let s' = add s m.me_name (`Path (EcPath.Pqname (scope, m'.me_name))) in
        (s', Th_module m')

  | Th_theory (x, th) ->
      let x'  = EcIdent.fresh x in
      let s'  = add s x (`Path (EcPath.Pqname (scope, x'))) in
      let th' = subst_theory s (EcPath.Pqname (scope, x')) th in
        (s', Th_theory (x', th'))

  | Th_export p -> (s, Th_export (subst_path s p))

(* -------------------------------------------------------------------- *)
and subst_theory (s : subst) (scope : EcPath.path) (items : theory) =
  let _, items =
    List.fold_left
      (fun (s, acc) item ->
        let (s, item) = subst_theory_item s scope item in
          (s, item :: acc))
      (s, []) items
  in
    List.rev items
