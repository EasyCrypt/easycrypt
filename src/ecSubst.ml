(* -------------------------------------------------------------------- *)
open EcUtils
open EcAst
open EcTypes
open EcDecl
open EcCoreFol
open EcModules
open EcTheory

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
  sb_module   : EcPath.mpath Mid.t;
  sb_path     : EcPath.path Mp.t;
  sb_tyvar    : ty Mid.t;
  sb_elocal   : expr Mid.t;
  sb_flocal   : EcCoreFol.form Mid.t;
  sb_fmem     : EcIdent.t Mid.t;
  sb_tydef    : (EcIdent.t list * ty) Mp.t;
  sb_def      : (EcIdent.t list * [`Op of  expr | `Pred of form]) Mp.t;
  sb_moddef   : EcPath.mpath Mp.t; (* Only top-level modules *)
}

(* -------------------------------------------------------------------- *)
let empty : subst = {
  sb_module   = Mid.empty;
  sb_path     = Mp.empty;
  sb_tyvar    = Mid.empty;
  sb_elocal   = Mid.empty;
  sb_flocal   = Mid.empty;
  sb_fmem     = Mid.empty;
  sb_tydef    = Mp.empty;
  sb_def      = Mp.empty;
  sb_moddef   = Mp.empty;
}

let is_empty s =
  Mid.is_empty s.sb_module
  && Mp.is_empty s.sb_path
  && Mid.is_empty s.sb_tyvar
  && Mid.is_empty s.sb_elocal
  && Mid.is_empty s.sb_flocal
  && Mid.is_empty s.sb_fmem
  && Mp.is_empty s.sb_tydef
  && Mp.is_empty s.sb_def
  && Mp.is_empty s.sb_moddef


(* -------------------------------------------------------------------- *)
let rec _subst_path (s : EcPath.path Mp.t) (p : EcPath.path) =
  match Mp.find_opt p s with
  | None -> begin
     match p.p_node with
     | Psymbol _ -> p
     | Pqname(q, x) -> EcPath.pqname (_subst_path s q) x
    end
  | Some q -> q

let subst_path (s : subst) (p : EcPath.path) = _subst_path s.sb_path p

(* -------------------------------------------------------------------- *)
let subst_mpath (s : subst) (mp : EcPath.mpath) =
  let rec doit s (mp : EcPath.mpath) =
      let args = List.map (doit s) mp.m_args in
      match mp.m_top with
      | `Concrete (p, sub) when Mp.mem p s.sb_moddef -> begin
        let s_p, s_sub, s_args =
          match Mp.find p s.sb_moddef with
          | { m_top = `Concrete (s_p, s_sub); m_args } -> (s_p, s_sub, m_args)
          | _ -> assert false in

        let cat_sub =
          match s_sub with
          | None -> sub
          | Some s_sub -> Some (EcPath.poappend s_sub sub) in

        EcPath.mpath_crt s_p (s_args @ mp.m_args) cat_sub
      end

      | `Concrete (p, sub) ->
        let p = _subst_path s.sb_path p in
        EcPath.mpath_crt p args sub

      | `Local id ->
         match Mid.find_opt id s.sb_module with
         | None -> EcPath.mpath_abs id args
         | Some mp -> EcPath.m_apply mp args
  in

  doit s mp

(* -------------------------------------------------------------------- *)
let subst_xpath (s : subst) (xp : EcPath.xpath) =
  EcPath.xpath (subst_mpath s xp.x_top) xp.x_sub

(* -------------------------------------------------------------------- *)
let subst_mem (s : subst) (m : EcIdent.t) =
  Mid.find_def m m s.sb_fmem

(* -------------------------------------------------------------------- *)
let get_opdef (s : subst) (p : EcPath.path) =
  match Mp.find_opt p s.sb_def with
  | Some (ids, `Op f) -> Some (ids, f) | _ -> None

(* -------------------------------------------------------------------- *)
let has_opdef (s : subst) (p : EcPath.path) =
  Option.is_some (get_opdef s p)

(* -------------------------------------------------------------------- *)
let get_def (s : subst) (p : EcPath.path) =
  match Mp.find_opt p s.sb_def with
  | Some (ids, body) ->
     let body =
       match body with
       | `Op   e -> form_of_expr mhr e
       | `Pred f -> f in
     Some (ids, body)

  | None -> None

(* -------------------------------------------------------------------- *)
let has_def (s : subst) (p : EcPath.path) =
  Mp.mem p s.sb_def

(* -------------------------------------------------------------------- *)
let add_tyvar (s : subst) (x : EcIdent.t) (ty : ty) =
  (* FIXME: check name clash *)
  let merger = function
    | None   -> Some ty
    | Some _ -> raise (SubstNameClash (`Ident x))
  in
  { s with sb_tyvar = Mid.change merger x s.sb_tyvar }

(* -------------------------------------------------------------------- *)
let add_tyvars (s : subst) (xs : EcIdent.t list) (tys : ty list) =
  List.fold_left2 add_tyvar s xs tys

(* -------------------------------------------------------------------- *)
let rec subst_ty (s : subst) (ty : ty) =
  match ty.ty_node with
  | Tglob mp ->
     tglob (EcPath.mget_ident (subst_mpath s (EcPath.mident mp)))

  | Tunivar _ ->
     ty                         (* FIXME *)

  | Tvar a ->
     Mid.find_def ty a s.sb_tyvar

  | Ttuple tys ->
     ttuple (subst_tys s tys)

  | Tconstr (p, tys) -> begin
      let tys = subst_tys s tys in

      match Mp.find_opt p s.sb_tydef with
      | None ->
         tconstr (subst_path s p) tys

      | Some (args, body) ->
         let s = List.fold_left2 add_tyvar empty args tys in
         subst_ty s body
    end

  | Tfun (t1, t2) ->
     tfun (subst_ty s t1) (subst_ty s t2)

(* -------------------------------------------------------------------- *)
and subst_tys (s : subst) (tys : ty list) =
  List.map (subst_ty s) tys

(* -------------------------------------------------------------------- *)
let add_module (s : subst) (x : EcIdent.t) (m : EcPath.mpath) =
  let merger = function
    | None   -> Some m
    | Some _ -> raise (SubstNameClash (`Ident x))
  in
    { s with sb_module = Mid.change merger x s.sb_module }

let add_elocal (s : subst) (x : EcIdent.t) (e : expr) =
  { s with sb_elocal = Mid.add x e s.sb_elocal }

let add_elocals (s : subst) (xs : EcIdent.t list) (es : expr list) =
  List.fold_left2 add_elocal s xs es

let fresh_elocal (s : subst) ((x, ty) : EcIdent.t * ty) =
  let xfresh = EcIdent.fresh x in
  let ty = subst_ty s ty in
  let s = add_elocal s x (e_local xfresh ty) in
  (s, (xfresh, ty))

let fresh_elocals (s : subst) (locals : (EcIdent.t * ty) list) =
  List.fold_left_map fresh_elocal s locals

let fresh_elocal_opt (s : subst) ((x, ty) : EcIdent.t option * ty) =
  match x with
  | None -> (s, (None, subst_ty s ty))
  | Some x ->
     let s, (x, ty) = fresh_elocal s (x, ty) in (s, (Some x, ty))

let fresh_elocals_opt (s : subst) (locals : (EcIdent.t option * ty) list) =
  List.fold_left_map fresh_elocal_opt s locals

let add_flocal (s : subst) (x : EcIdent.t) (f : EcCoreFol.form) =
  { s with sb_flocal = Mid.add x f s.sb_flocal }

let add_flocals (s : subst) (xs : EcIdent.t list) (fs : EcCoreFol.form list) =
  List.fold_left2 add_flocal s xs fs

let fresh_flocal (s : subst) ((x, ty) : EcIdent.t * ty) =
  let xfresh = EcIdent.fresh x in
  let ty = subst_ty s ty in
  let s = add_flocal s x (EcCoreFol.f_local xfresh ty) in
  (s, (xfresh, ty))

let fresh_flocals (s : subst) (locals : (EcIdent.t * ty) list) =
  List.fold_left_map fresh_flocal s locals

let fresh_flocal_opt (s : subst) ((x, ty) : EcIdent.t option * ty) =
  match x with
  | None -> (s, (None, subst_ty s ty))
  | Some x ->
     let s, (x, ty) = fresh_flocal s (x, ty) in (s, (Some x, ty))

let fresh_flocals_opt (s : subst) (locals : (EcIdent.t option * ty) list) =
  List.fold_left_map fresh_flocal_opt s locals

let rename_flocal (s : subst) xfrom xto ty =
  let xf = EcCoreFol.f_local xto ty in
  let xe = EcTypes.e_local xto ty in
  let s  = add_flocal s xfrom xf in

  let merger o = assert (o = None); Some xe in
  { s with sb_elocal = Mid.change merger xfrom s.sb_elocal }

let add_memory (s : subst) (m : EcIdent.t) (target : EcIdent.t) =
  { s with sb_fmem = Mid.add m target s.sb_fmem }

let fresh_memory (s : subst) (m : EcIdent.t) =
  let mfresh = EcIdent.fresh m in
  (add_memory s m mfresh, mfresh)

let fresh_memtype (s : subst) ((m, mt) : EcMemory.memenv) =
  let mt = EcMemory.mt_subst (subst_ty s) mt in
  let s, mfresh = fresh_memory s m in
  (s, (mfresh, mt))

let subst_memtype (s : subst) ((m, mt) : EcMemory.memenv) =
  let mt = EcMemory.mt_subst (subst_ty s) mt in
  (s, (m, mt))

let add_path (s : subst) ~src ~dst =
  assert (Mp.find_opt src s.sb_path = None);
  { s with sb_path = Mp.add src dst s.sb_path }

let add_tydef (s : subst) p (ids, ty) =
  assert (Mp.find_opt p s.sb_tydef = None);
  { s with sb_tydef = Mp.add p (ids, ty) s.sb_tydef }

let add_opdef (s : subst) p (ids, f) =
  assert (Mp.find_opt p s.sb_def = None);
  { s with sb_def = Mp.add p (ids, (`Op f)) s.sb_def }

let add_pddef (s : subst) p (ids, f) =
  assert (Mp.find_opt p s.sb_def = None);
  { s with sb_def = Mp.add p (ids, `Pred f) s.sb_def }

let add_moddef (s : subst) ~(src : EcPath.path) ~(dst : EcPath.mpath) =
  assert (Mp.find_opt src s.sb_moddef = None);
  assert (EcPath.is_concrete dst);
  { s with sb_moddef = Mp.add src dst s.sb_moddef }

(* -------------------------------------------------------------------- *)
let subst_flocal (s : subst) (f : form) =
  match f.f_node with
  | Flocal id -> begin
      match Mid.find id s.sb_flocal with
      | f -> f
      | exception Not_found -> f
      end
  | _ -> assert false

(* -------------------------------------------------------------------- *)
let subst_progvar (s : subst) (pv : prog_var) =
  match pv with
  | PVloc _ -> pv
  | PVglob xp -> pv_glob (subst_xpath s xp)

(* -------------------------------------------------------------------- *)
let subst_expr_lpattern (s : subst) (lp : lpattern) =
  match lp with
  | LSymbol x ->
     let s, x = fresh_elocal s x in
     (s, LSymbol x)

  | LTuple xs ->
      let (s, xs) = fresh_elocals s xs in
      (s, LTuple xs)

  | LRecord (p, xs) ->
      let (s, xs) = fresh_elocals_opt s xs in
      (s, LRecord (subst_path s p, xs))

(* -------------------------------------------------------------------- *)
let rec subst_expr (s : subst) (e : expr) =
  match e.e_node with
  | Elocal id -> begin
      match Mid.find id s.sb_elocal with
      | aout -> aout
      | exception Not_found -> e_local id (subst_ty s e.e_ty)
    end

  | Evar pv ->
     e_var (subst_progvar s pv) (subst_ty s e.e_ty)

  | Eapp ({ e_node = Eop (p, tys) }, args) when has_opdef s p ->
      let tys  = subst_tys s tys in
      let ty   = subst_ty  s e.e_ty in
      let body = oget (get_opdef s p) in
      let args = List.map (subst_expr s) args in
      subst_eop ty tys args body

  | Eop (p, tys) when has_opdef s p ->
      let tys  = subst_tys s tys in
      let ty   = subst_ty  s e.e_ty in
      let body = oget (get_opdef s p) in
      subst_eop ty tys [] body

  | Eop (p, tys) ->
      let p   = subst_path s p in
      let tys = subst_tys s tys in
      let ty  = subst_ty s e.e_ty in
      e_op p tys ty

  | Elet (lp, e1, e2) ->
      let e1 = subst_expr s e1 in
      let s, lp = subst_expr_lpattern s lp in
      let e2 = subst_expr s e2 in
      e_let lp e1 e2

  | Equant (q, b, e1) ->
      let s, b = fresh_elocals s b in
      let e1 = subst_expr s e1 in
      e_quantif q b e1

  | _ -> e_map (subst_ty s) (subst_expr s) e

(* -------------------------------------------------------------------- *)
and subst_eop ety tys args (tyids, e) =
  let s = add_tyvars empty tyids tys in

  let (s, args, e) =
    match e.e_node with
    | Equant (`ELambda, largs, lbody) when args <> [] ->
        let largs1, largs2 = List.takedrop (List.length args  ) largs in
        let  args1,  args2 = List.takedrop (List.length largs1)  args in
        (add_elocals s (List.fst largs1) args1, args2, e_lam largs2 lbody)

    | _ -> (s, args, e)
  in

  e_app (subst_expr s e) args ety

(* -------------------------------------------------------------------- *)
let subst_lv (s : subst) (lv : lvalue) =
  let for1 (pv, ty) = (subst_progvar s pv, subst_ty s ty) in

  match lv with
  | LvVar pvty ->
     LvVar (for1 pvty)

  | LvTuple pvtys ->
     LvTuple (List.map for1 pvtys)

(* -------------------------------------------------------------------- *)
let rec subst_stmt (s : subst) (st : stmt) : stmt =
  stmt (List.map (subst_instr s) st.s_node)

(* -------------------------------------------------------------------- *)
and subst_instr (s : subst) (i : instr) : instr =
  match i.i_node with
  | Sasgn (lv, e) ->
     i_asgn (subst_lv s lv, subst_expr s e)

  | Srnd (lv, e) ->
     i_rnd (subst_lv s lv, subst_expr s e)

  | Scall (lv, p, args) ->
     let lv = omap (subst_lv s) lv in
     let p = subst_xpath s p in
     let args = List.map (subst_expr s) args in
     i_call (lv, p, args)

  | Sif (e, s1, s2) ->
     let e = subst_expr s e in
     let s1 = subst_stmt s s1 in
     let s2 = subst_stmt s s2 in
     i_if (e, s1, s2)

  | Swhile (e, body) ->
     let e = subst_expr s e in
     let body = subst_stmt s body in
     i_while (e, body)

  | Smatch (e, bs) ->
     let subst_branch (ids, body) =
       let s, ids = fresh_elocals s ids in
       (ids, subst_stmt s body) in

     let e = subst_expr s e in
     let bs = List.map subst_branch bs in

     i_match (e, bs)

  | Sassert e ->
     i_assert (subst_expr s e)

  | Sabstract _ ->
     i

(* -------------------------------------------------------------------- *)
let subst_ovariable (s : subst) (x : ovariable) =
  { x with ov_type = subst_ty s x.ov_type; }

let subst_variable (s : subst) (x : variable) =
  { x with v_type = subst_ty s x.v_type; }

(* -------------------------------------------------------------------- *)
let subst_fun_uses (s : subst) (u : uses) =
  let x_subst = subst_xpath s in
  let calls  = List.map x_subst u.us_calls
  and reads  = Sx.fold (fun p m -> Sx.add (x_subst p) m) u.us_reads Sx.empty
  and writes = Sx.fold (fun p m -> Sx.add (x_subst p) m) u.us_writes Sx.empty in
  EcModules.mk_uses calls reads writes

(* -------------------------------------------------------------------- *)
let subst_funsig (s : subst) (funsig : funsig) =
  let fs_arg = subst_ty s funsig.fs_arg in
  let fs_ret = subst_ty s funsig.fs_ret in
  let fs_anm = List.map (subst_ovariable s) funsig.fs_anames in

  { fs_name   = funsig.fs_name;
    fs_arg    = fs_arg;
    fs_anames = fs_anm;
    fs_ret    = fs_ret; }

(* -------------------------------------------------------------------- *)
let subst_form_lpattern (s : subst) (lp : lpattern) =
  match lp with
  | LSymbol x ->
     let s, x = fresh_flocal s x in
     (s, LSymbol x)

  | LTuple xs ->
      let (s, xs) = fresh_flocals s xs in
      (s, LTuple xs)

  | LRecord (p, xs) ->
      let (s, xs) = fresh_flocals_opt s xs in
      (s, LRecord (subst_path s p, xs))

(* -------------------------------------------------------------------- *)
let rec subst_form (s : subst) (f : form) =
  match f.f_node with
  | Fquant (q, b, f1) ->
      let s, b = fresh_glocals s b in
      let e1 = subst_form s f1 in
      f_quant q b e1

  | Fmatch (f, bs, ty) ->
     let f = subst_form s f in
     let bs = List.map (subst_form s) bs in
     let ty = subst_ty s ty in
     f_match f bs ty

  | Flet (lp, f, body) ->
      let f = subst_form s f in
      let s, lp = subst_form_lpattern s lp in
      let body = subst_form s body in
      f_let lp f body

  | Flocal x -> begin
      match Mid.find x s.sb_flocal with
      | aout -> aout
      | exception Not_found -> f_local x (subst_ty s f.f_ty)
    end

  | Fpvar (pv, m) ->
     let pv = subst_progvar s pv in
     let ty = subst_ty s f.f_ty in
     let m = subst_mem s m in
     f_pvar pv ty m

  | Fglob (mp, m) ->
     let mp = EcPath.mget_ident (subst_mpath s (EcPath.mident mp)) in
     let m = subst_mem s m in
     f_glob mp m

  | Fapp ({ f_node = Fop (p, tys) }, args) when has_def s p ->
      let tys  = subst_tys s tys in
      let ty   = subst_ty  s f.f_ty in
      let body = oget (get_def s p) in
      let args = List.map (subst_form s) args in
      subst_fop ty tys args body

  | Fop (p, tys) when has_def s p ->
      let tys  = subst_tys s tys in
      let ty   = subst_ty  s f.f_ty in
      let body = oget (get_def s p) in
      subst_fop ty tys [] body

  | Fop (p, tys) ->
      let p   = subst_path s p in
      let tys = subst_tys s tys in
      let ty  = subst_ty s f.f_ty in
      f_op p tys ty

  | FhoareF { hf_pr; hf_f; hf_po } ->
     let hf_pr, hf_po =
       let s = add_memory s mhr mhr in
       let hf_pr = subst_form s hf_pr in
       let hf_po = subst_form s hf_po in
       (hf_pr, hf_po) in
     let hf_f  = subst_xpath s hf_f in
     f_hoareF hf_pr hf_f hf_po

  | FhoareS { hs_m; hs_pr; hs_s; hs_po } ->
     let hs_m, (hs_pr, hs_po) =
       let s, hs_m = subst_memtype s hs_m in
       let hs_pr = subst_form s hs_pr in
       let hs_po = subst_form s hs_po in
       hs_m, (hs_pr, hs_po) in
     let hs_s = subst_stmt s hs_s in
     f_hoareS hs_m hs_pr hs_s hs_po

  | FbdHoareF { bhf_pr; bhf_f; bhf_po; bhf_cmp; bhf_bd } ->
     let bhf_pr, bhf_po =
       let s = add_memory s mhr mhr in
       let bhf_pr = subst_form s bhf_pr in
       let bhf_po = subst_form s bhf_po in
       (bhf_pr, bhf_po) in
     let bhf_f  = subst_xpath s bhf_f in
     let bhf_bd  = subst_form s bhf_bd in
     f_bdHoareF bhf_pr bhf_f bhf_po bhf_cmp bhf_bd

  | FbdHoareS { bhs_m; bhs_pr; bhs_s; bhs_po; bhs_cmp; bhs_bd } ->
     let bhs_m, (bhs_pr, bhs_po, bhs_bd) =
       let s, bhs_m = subst_memtype s bhs_m in
       let bhs_pr = subst_form s bhs_pr in
       let bhs_po = subst_form s bhs_po in
       let bhs_bd = subst_form s bhs_bd in
       bhs_m, (bhs_pr, bhs_po, bhs_bd) in
     let bhs_s = subst_stmt s bhs_s in
     f_bdHoareS bhs_m bhs_pr bhs_s bhs_po bhs_cmp bhs_bd

   | FeHoareF { ehf_pr; ehf_f; ehf_po } ->
     let ehf_pr, ehf_po =
       let s = add_memory s mhr mhr in
       let ehf_pr = subst_form s ehf_pr in
       let ehf_po = subst_form s ehf_po in
       (ehf_pr, ehf_po) in
     let ehf_f  = subst_xpath s ehf_f in
     f_eHoareF ehf_pr ehf_f ehf_po

  | FeHoareS { ehs_m; ehs_pr; ehs_s; ehs_po } ->
     let ehs_m, (ehs_pr, ehs_po) =
       let s, ehs_m = subst_memtype s ehs_m in
       let ehs_pr = subst_form s ehs_pr in
       let ehs_po = subst_form s ehs_po in
       ehs_m, (ehs_pr, ehs_po) in
     let ehs_s = subst_stmt s ehs_s in
     f_eHoareS ehs_m ehs_pr ehs_s ehs_po

  | FequivF { ef_pr; ef_fl; ef_fr; ef_po } ->
     let ef_pr, ef_po =
       let s = add_memory s mleft mleft in
       let s = add_memory s mright mright in
       let ef_pr = subst_form s ef_pr in
       let ef_po = subst_form s ef_po in
       (ef_pr, ef_po) in
     let ef_fl = subst_xpath s ef_fl in
     let ef_fr = subst_xpath s ef_fr in
     f_equivF ef_pr ef_fl ef_fr ef_po

  | FequivS { es_ml; es_mr; es_pr; es_sl; es_sr; es_po } ->
     let (es_ml, es_mr), (es_pr, es_po) =
       let s, es_ml = subst_memtype s es_ml in
       let s, es_mr = subst_memtype s es_mr in
       let es_pr = subst_form s es_pr in
       let es_po = subst_form s es_po in
       (es_ml, es_mr), (es_pr, es_po) in
     let es_sl = subst_stmt s es_sl in
     let es_sr = subst_stmt s es_sr in
     f_equivS es_ml es_mr es_pr es_sl es_sr es_po

  | FeagerF { eg_pr; eg_sl; eg_fl; eg_fr; eg_sr; eg_po } ->
     let eg_pr, eg_po =
       let s = add_memory s mleft  mleft  in
       let s = add_memory s mright mright in
       let eg_pr = subst_form s eg_pr in
       let eg_po = subst_form s eg_po in
       (eg_pr, eg_po) in
     let eg_sl = subst_stmt s eg_sl in
     let eg_sr = subst_stmt s eg_sr in
     let eg_fl = subst_xpath s eg_fl in
     let eg_fr = subst_xpath s eg_fr in
     f_eagerF eg_pr eg_sl eg_fl eg_fr eg_sr eg_po

  | Fpr { pr_mem; pr_fun; pr_args; pr_event } ->
     let pr_mem = subst_mem s pr_mem in
     let pr_fun = subst_xpath s pr_fun in
     let pr_args = subst_form s pr_args in
     let pr_event =
       let s = add_memory s mhr mhr in
       subst_form s pr_event in
     f_pr pr_mem pr_fun pr_args pr_event

  | Fif _ | Fint _ | Ftuple _ | Fproj _ | Fapp _ ->
     f_map (subst_ty s) (subst_form s) f

(* -------------------------------------------------------------------- *)
and subst_fop fty tys args (tyids, f) =
  let s = add_tyvars empty tyids tys in

  let (s, args, f) =
    match f.f_node with
    | Fquant (Llambda, largs, lbody) when args <> [] ->
        let largs1, largs2 = List.takedrop (List.length args  ) largs in
        let  args1,  args2 = List.takedrop (List.length largs1)  args in
        (add_flocals s (List.fst largs1) args1, args2, f_lambda largs2 lbody)

    | _ -> (s, args, f)
  in

  f_app (subst_form s f) args fty

(* -------------------------------------------------------------------- *)
and subst_oracle_info (s : subst) (oi : OI.t) =
  OI.mk (List.map (subst_xpath s) (PreOI.allowed oi))

(* -------------------------------------------------------------------- *)
and subst_oracle_infos (s : subst) (ois : oracle_infos) =
  EcSymbols.Msym.map (fun oi -> subst_oracle_info s oi) ois

    (* -------------------------------------------------------------------- *)
and subst_mod_restr (s : subst) (mr : mod_restr) =
  let subst_ (xs, ms) = Sx.map (subst_xpath s) xs, Sm.map (subst_mpath s) ms in
  ur_app subst_ mr

(* -------------------------------------------------------------------- *)
and subst_modsig_body_item (s : subst) (item : module_sig_body_item) =
  match item with
  | Tys_function funsig -> Tys_function (subst_funsig s funsig)

(* -------------------------------------------------------------------- *)
and subst_modsig_body (s : subst) (sbody : module_sig_body) =
  List.map (subst_modsig_body_item s) sbody

(* -------------------------------------------------------------------- *)
and subst_modsig ?params (s : subst) (comps : module_sig) =
  let sbody, newparams =
    match params with
    | None -> begin
        match comps.mis_params with
        | [] -> (s, [])
        | _  ->
            List.map_fold
              (fun (s : subst) (a, aty) ->
                let a'   = EcIdent.fresh a in
                let decl = (a', subst_modtype s aty) in
                add_module s a (EcPath.mident a'), decl)
              s comps.mis_params
    end

  | Some params ->
      List.map_fold
        (fun (s : subst) ((a, aty), a') ->
            let decl = (a', subst_modtype s aty) in
            add_module s a (EcPath.mident a'), decl)
          s (List.combine comps.mis_params params)
  in

  let comps =
    { mis_params = newparams;
      mis_body   = subst_modsig_body sbody comps.mis_body;
      mis_oinfos = subst_oracle_infos sbody comps.mis_oinfos; }
  in
    (sbody, comps)

(* -------------------------------------------------------------------- *)
and subst_modtype (s : subst) (modty : module_type) =
  let mt_name =
    ofdfl
      (fun () -> subst_path s modty.mt_name)
      (Mp.find_opt modty.mt_name s.sb_path) in

  { mt_params = List.map (snd_map (subst_modtype s)) modty.mt_params;
    mt_name   = mt_name;
    mt_args   = List.map (subst_mpath s) modty.mt_args; }


(* -------------------------------------------------------------------- *)
and subst_mty_mr (s : subst) ((mty, mr) : mty_mr) =
  subst_modtype s mty, subst_mod_restr s mr

(* -------------------------------------------------------------------- *)
and subst_gty (s : subst) (ty : gty) =
  match ty with
  | GTty ty ->
     GTty (subst_ty s ty)

  | GTmodty mty ->
     GTmodty (subst_mty_mr s mty)

  | GTmem m ->
     GTmem (EcMemory.mt_subst (subst_ty s) m)

(* -------------------------------------------------------------------- *)
and fresh_glocal (s : subst) ((x, ty) : EcIdent.t * gty) =
  let xfresh = EcIdent.fresh x in
  let gty = subst_gty s ty in
  match gty with
  | GTty ty ->
     let s = add_flocal s x (f_local xfresh ty) in
     s, (xfresh, gty)
  | GTmem _ ->
     s, (x, gty)
  | GTmodty _ ->
     let s = add_module s x (EcPath.mident xfresh) in
     s, (xfresh, gty)

(* -------------------------------------------------------------------- *)
and fresh_glocals (s : subst) (locals : (EcIdent.t * gty) list) : subst * _ =
  List.fold_left_map fresh_glocal s locals

(* -------------------------------------------------------------------- *)
and subst_top_modsig (s : subst) (ms : top_module_sig) =
  { tms_sig  = snd (subst_modsig s ms.tms_sig);
    tms_loca = ms.tms_loca; }

(* -------------------------------------------------------------------- *)
and subst_function_def (s : subst) (def : function_def) =
  { f_locals = List.map (subst_variable s) def.f_locals;
    f_body   = subst_stmt s def.f_body;
    f_ret    = omap (subst_expr s) def.f_ret;
    f_uses   = subst_fun_uses s def.f_uses; }

(* -------------------------------------------------------------------- *)
and subst_function (s : subst) (f : function_) =
  let sig' = subst_funsig s f.f_sig in
  let def' =
    match f.f_def with
    | FBdef def -> FBdef (subst_function_def s def)
    | FBalias f -> FBalias (subst_xpath s f)
    | FBabs oi  -> FBabs (subst_oracle_info s oi) in
  { f_name = f.f_name;
    f_sig  = sig';
    f_def  = def' }

(* -------------------------------------------------------------------- *)
and subst_module_item (s : subst) (item : module_item) =
  match item with
  | MI_Module m ->
      let m' = subst_module s m in
      MI_Module m'

  | MI_Variable x ->
      let x' = subst_variable s x in
      MI_Variable x'

  | MI_Function f ->
      let f' = subst_function s f in
      MI_Function f'

(* -------------------------------------------------------------------- *)
and subst_module_items (s : subst) (items : module_item list) =
  List.map (subst_module_item s) items

(* -------------------------------------------------------------------- *)
and subst_module_struct (s : subst) (bstruct : module_structure) =
    { ms_body   = subst_module_items s bstruct.ms_body; }

(* -------------------------------------------------------------------- *)
and subst_module_body (s : subst) (body : module_body) =
  match body with
  | ME_Alias (arity,m) ->
      ME_Alias (arity, subst_mpath s m)

  | ME_Structure bstruct ->
      ME_Structure (subst_module_struct s bstruct)

  | ME_Decl p -> ME_Decl (subst_mty_mr s p)

(* -------------------------------------------------------------------- *)
and subst_module_comps (s : subst) (comps : module_comps) =
  (subst_module_items s comps : module_comps)

(* -------------------------------------------------------------------- *)
and subst_module (s : subst) (m : module_expr) =
  let sbody, me_params = match m.me_params with
    | [] -> (s, [])
    | _  ->
        List.map_fold
          (fun (s : subst) (a, aty) ->
            let a'   = EcIdent.fresh a in
            let decl = (a', subst_modtype s aty) in
            add_module s a (EcPath.mident a'), decl)
        s m.me_params in

  let me_body = subst_module_body sbody m.me_body in
  let me_comps = subst_module_comps sbody m.me_comps in
  let me_sig_body = subst_modsig_body sbody m.me_sig_body in
  let me_oinfos = subst_oracle_infos sbody m.me_oinfos in
  { me_name = m.me_name; me_params; me_body; me_comps; me_sig_body; me_oinfos; }

(* -------------------------------------------------------------------- *)
let subst_modsig ?params (s : subst) (comps : module_sig) =
  snd (subst_modsig ?params s comps)

(* -------------------------------------------------------------------- *)
let subst_top_module (s : subst) (m : top_module_expr) =
  { tme_expr = subst_module s m.tme_expr;
    tme_loca = m.tme_loca; }

(* -------------------------------------------------------------------- *)
let subst_typeclass (s : subst) (tcs : Sp.t) =
  Sp.map (subst_path s) tcs

(* -------------------------------------------------------------------- *)
let fresh_tparam (s : subst) ((x, tcs) : ty_param) =
  let newx = EcIdent.fresh x in
  let tcs  = subst_typeclass s tcs in
  let s    = add_tyvar s x (tvar newx) in
  (s, (newx, tcs))

(* -------------------------------------------------------------------- *)
let fresh_tparams (s : subst) (tparams : ty_params) =
  List.fold_left_map fresh_tparam s tparams

(* -------------------------------------------------------------------- *)
let subst_genty (s : subst) (tparams, ty) =
  let s, tparams = fresh_tparams s tparams in
  let ty = subst_ty s ty in
  (tparams, ty)

(* -------------------------------------------------------------------- *)
let subst_tydecl_body (s : subst) (tyd : ty_body) =
  match tyd with
  | `Abstract tc ->
      `Abstract (subst_typeclass s tc)

  | `Concrete ty ->
      `Concrete (subst_ty s ty)

  | `Datatype dtype ->
      let dtype =
        { tydt_ctors   = List.map (snd_map (List.map (subst_ty s))) dtype.tydt_ctors;
          tydt_schelim = subst_form s dtype.tydt_schelim;
          tydt_schcase = subst_form s dtype.tydt_schcase; }
      in `Datatype dtype

  | `Record (scheme, fields) ->
      `Record (subst_form s scheme, List.map (snd_map (subst_ty s)) fields)

(* -------------------------------------------------------------------- *)
let subst_tydecl (s : subst) (tyd : tydecl) =
  let s, tparams = fresh_tparams s tyd.tyd_params in
  let body = subst_tydecl_body s tyd.tyd_type in

  { tyd_params  = tparams;
    tyd_type    = body;
    tyd_loca    = tyd.tyd_loca; }

(* -------------------------------------------------------------------- *)
let rec subst_op_kind (s : subst) (kind : operator_kind) =
  match kind with
  | OB_oper (Some body) ->
      OB_oper (Some (subst_op_body s body))

  | OB_pred (Some body) ->
      OB_pred (Some (subst_pr_body s body))

  | OB_nott nott ->
     OB_nott (subst_notation s nott)

  | OB_oper None | OB_pred None -> kind

and subst_notation (s : subst) (nott : notation) =
  let s, xs = fresh_elocals s nott.ont_args in
  { ont_args  = xs;
    ont_resty = subst_ty s nott.ont_resty;
    ont_body  = subst_expr s nott.ont_body;
    ont_ponly = nott.ont_ponly; }

and subst_op_body (s : subst) (bd : opbody) =
  match bd with
  | OP_Plain body ->
      OP_Plain (subst_form s body)

  | OP_Constr (p, i)  -> OP_Constr (subst_path s p, i)
  | OP_Record p       -> OP_Record (subst_path s p)
  | OP_Proj (p, i, j) -> OP_Proj (subst_path s p, i, j)

  | OP_Fix opfix ->
      let (es, args) = fresh_elocals s opfix.opf_args in

      OP_Fix { opf_args     = args;
               opf_resty    = subst_ty s opfix.opf_resty;
               opf_struct   = opfix.opf_struct;
               opf_branches = subst_branches es opfix.opf_branches; }

  | OP_TC -> OP_TC

and subst_branches (s : subst) = function
  | OPB_Leaf (locals, e) ->
      let (s, locals) = List.map_fold fresh_elocals s locals in
      OPB_Leaf (locals, subst_expr s e)

  | OPB_Branch bs ->
      let for1 b =
        let (ctorp, ctori) = b.opb_ctor in
          { opb_ctor = (subst_path s ctorp, ctori);
            opb_sub  = subst_branches s b.opb_sub; }
      in
        OPB_Branch (Parray.map for1 bs)

and subst_pr_body (s : subst) (bd : prbody) =
  match bd with
  | PR_Plain body ->
      PR_Plain (subst_form s body)

  | PR_Ind ind ->
      let args    = List.map (snd_map gtty) ind.pri_args in
      let s, args = fresh_glocals s args in
      let args    = List.map (snd_map gty_as_ty) args in
      let ctors   =
        let for1 ctor =
          let s, bds = fresh_glocals s ctor.prc_bds in
          let spec   = List.map (subst_form s) ctor.prc_spec in
          { ctor with prc_bds = bds; prc_spec = spec; }
        in List.map for1 ind.pri_ctors

      in PR_Ind { pri_args = args; pri_ctors = ctors; }

(* -------------------------------------------------------------------- *)
let subst_op (s : subst) (op : operator) =
  let s, tparams = fresh_tparams s op.op_tparams in
  let opty = subst_ty s op.op_ty in
  let kind = subst_op_kind s op.op_kind in

  { op_tparams  = tparams       ;
    op_ty       = opty          ;
    op_kind     = kind          ;
    op_loca     = op.op_loca    ;
    op_opaque   = op.op_opaque  ;
    op_clinline = op.op_clinline;
    op_unfold   = op.op_unfold  ; }

(* -------------------------------------------------------------------- *)
let subst_ax (s : subst) (ax : axiom) =
  let s, tparams = fresh_tparams s ax.ax_tparams in
  let spec   = subst_form s ax.ax_spec in

  { ax_tparams = tparams;
    ax_spec    = spec;
    ax_kind    = ax.ax_kind;
    ax_loca    = ax.ax_loca;
    ax_smt     = ax.ax_smt; }

(* -------------------------------------------------------------------- *)
let fresh_scparam (s : subst) ((x, ty) : EcIdent.t * ty) =
  let newx = EcIdent.fresh x in
  let ty = subst_ty s ty in
  let s = add_elocal s x (e_local newx ty) in
  let s = add_flocal s x (f_local newx ty) in
  (s, (newx, ty))

(* -------------------------------------------------------------------- *)
let fresh_scparams (s : subst) (xtys : (EcIdent.t * ty) list) =
  List.fold_left_map fresh_scparam s xtys

(* -------------------------------------------------------------------- *)
let subst_ring (s : subst) cr =
  { r_type  = subst_ty s cr.r_type;
    r_zero  = subst_path s cr.r_zero;
    r_one   = subst_path s cr.r_one;
    r_add   = subst_path s cr.r_add;
    r_opp   = omap (subst_path s) cr.r_opp;
    r_mul   = subst_path s cr.r_mul;
    r_exp   = omap (subst_path s) cr.r_exp;
    r_sub   = omap (subst_path s) cr.r_sub;
    r_embed =
      begin match cr.r_embed with
      | `Direct  -> `Direct
      | `Default -> `Default
      | `Embed p -> `Embed (subst_path s p)
      end;
    r_kind = cr.r_kind
  }

(* -------------------------------------------------------------------- *)
let subst_field (s : subst) cr =
  { f_ring = subst_ring s cr.f_ring;
    f_inv  = subst_path s cr.f_inv;
    f_div  = omap (subst_path s) cr.f_div; }

(* -------------------------------------------------------------------- *)
let subst_instance (s : subst) tci =
  match tci with
  | `Ring    cr -> `Ring  (subst_ring  s cr)
  | `Field   cr -> `Field (subst_field s cr)
  | `General p  -> `General (subst_path s p)

(* -------------------------------------------------------------------- *)
let subst_tc (s : subst) tc =
  let tc_prt = omap (subst_path s) tc.tc_prt in
  let tc_ops = List.map (snd_map (subst_ty s)) tc.tc_ops in
  let tc_axs = List.map (snd_map (subst_form s)) tc.tc_axs in
    { tc_prt; tc_ops; tc_axs; tc_loca = tc.tc_loca }

(* -------------------------------------------------------------------- *)
(* SUBSTITUTION OVER THEORIES *)
let rec subst_theory_item_r (s : subst) (item : theory_item_r) =
  match item with
  | Th_type (x, tydecl) ->
      Th_type (x, subst_tydecl s tydecl)

  | Th_operator (x, op) ->
      Th_operator (x, subst_op s op)

  | Th_axiom (x, ax) ->
      Th_axiom (x, subst_ax s ax)

  | Th_modtype (x, tymod) ->
      Th_modtype (x, subst_top_modsig s tymod)

  | Th_module m ->
      Th_module (subst_top_module s m)

  | Th_theory (x, th) ->
      Th_theory (x, subst_ctheory s th)

  | Th_export (p, lc) ->
      Th_export (subst_path s p, lc)

  | Th_instance (ty, tci, lc) ->
      Th_instance (subst_genty s ty, subst_instance s tci, lc)

  | Th_typeclass (x, tc) ->
      Th_typeclass (x, subst_tc s tc)

  | Th_baserw _ ->
      item

  | Th_addrw (b, ls, lc) ->
      Th_addrw (subst_path s b, List.map (subst_path s) ls, lc)

  | Th_reduction rules ->
      let rules =
        List.map (fun (p, opts, _) -> (subst_path s p, opts, None)) rules
      in Th_reduction rules

  | Th_auto ({ axioms } as auto_rl) ->
      Th_auto { auto_rl with axioms =
        List.map (fst_map (subst_path s)) axioms }

  | Th_alias (name, target) ->
      Th_alias (name, subst_path s target)

(* -------------------------------------------------------------------- *)
and subst_theory (s : subst) (items : theory) =
  List.map (subst_theory_item s) items

(* -------------------------------------------------------------------- *)
and subst_theory_item (s : subst) (item : theory_item) =
  { ti_item   = subst_theory_item_r s item.ti_item;
    ti_import = item.ti_import; }

(* -------------------------------------------------------------------- *)
and subst_ctheory (s : subst) (cth : ctheory) =
  { cth_items  = subst_theory s cth.cth_items;
    cth_loca   = cth.cth_loca;
    cth_mode   = cth.cth_mode;
    cth_source = omap (subst_theory_source s) cth.cth_source; }

(* -------------------------------------------------------------------- *)
and subst_theory_source (s : subst) (ths : thsource) =
  { ths_base = subst_path s ths.ths_base; }

(* -------------------------------------------------------------------- *)
let init_tparams (params : (EcIdent.t * ty) list) : subst =
  List.fold_left (fun s (x, ty) -> add_tyvar s x ty) empty params

(* -------------------------------------------------------------------- *)
let open_oper op tys =
  let s = List.combine (List.fst op.op_tparams) tys in
  let s = init_tparams s in
  (subst_ty s op.op_ty, subst_op_kind s op.op_kind)

let open_tydecl tyd tys =
  let s = List.combine (List.fst tyd.tyd_params) tys in
  let s = init_tparams s in
  subst_tydecl_body s tyd.tyd_type

(* -------------------------------------------------------------------- *)
let freshen_type (tparams, ty) =
  let s, tparams = fresh_tparams empty tparams in
  (tparams, subst_ty s ty)
