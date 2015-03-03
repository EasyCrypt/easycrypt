(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcIdent
open EcTypes

open EcModules

type memory = EcMemory.memory

module BI = EcBigInt
module Mp = EcPath.Mp
module Sp = EcPath.Sp
module Sm = EcPath.Sm
module Sx = EcPath.Sx

open EcBigInt.Notations

(* -------------------------------------------------------------------- *)
type gty =
  | GTty    of EcTypes.ty
  | GTmodty of module_type * mod_restr
  | GTmem   of EcMemory.memtype

type quantif =
  | Lforall
  | Lexists
  | Llambda

type binding  = (EcIdent.t * gty)
type bindings = binding list

let mhr    = EcIdent.create "&hr"
let mleft  = EcIdent.create "&1"
let mright = EcIdent.create "&2"

type hoarecmp = FHle | FHeq | FHge

type form = {
  f_node : f_node;
  f_ty   : ty;
  f_fv   : int EcIdent.Mid.t; (* local, memory, module ident *)
  f_tag  : int;
}

and f_node =
  | Fquant  of quantif * bindings * form
  | Fif     of form * form * form
  | Flet    of lpattern * form * form
  | Fint    of BI.zint
  | Flocal  of EcIdent.t
  | Fpvar   of EcTypes.prog_var * memory
  | Fglob   of EcPath.mpath     * memory
  | Fop     of EcPath.path * ty list
  | Fapp    of form * form list
  | Ftuple  of form list
  | Fproj   of form * int
  | FhoareF of hoareF (* $hr / $hr *)
  | FhoareS of hoareS

  | FbdHoareF of bdHoareF (* $hr / $hr *)
  | FbdHoareS of bdHoareS

  | FequivF of equivF (* $left,$right / $left,$right *)
  | FequivS of equivS

  | FeagerF of eagerF

  | Fpr of pr (* hr *)

and eagerF = {
  eg_pr : form;
  eg_sl : stmt;  (* No local program variables *)
  eg_fl : EcPath.xpath;
  eg_fr : EcPath.xpath;
  eg_sr : stmt;  (* No local program variables *)
  eg_po : form
}

and equivF = {
  ef_pr : form;
  ef_fl : EcPath.xpath;
  ef_fr : EcPath.xpath;
  ef_po : form;
}

and equivS = {
  es_ml  : EcMemory.memenv;
  es_mr  : EcMemory.memenv;
  es_pr  : form;
  es_sl  : stmt;
  es_sr  : stmt;
  es_po  : form; }

and hoareF = {
  hf_pr : form;
  hf_f  : EcPath.xpath;
  hf_po : form;
}
and hoareS = {
  hs_m  : EcMemory.memenv;
  hs_pr : form;
  hs_s  : stmt;
  hs_po : form; }

and bdHoareF = {
  bhf_pr  : form;
  bhf_f   : EcPath.xpath;
  bhf_po  : form;
  bhf_cmp : hoarecmp;
  bhf_bd  : form;
}
and bdHoareS = {
  bhs_m   : EcMemory.memenv;
  bhs_pr  : form;
  bhs_s   : stmt;
  bhs_po  : form;
  bhs_cmp : hoarecmp;
  bhs_bd  : form;
}

and pr = {
  pr_mem   : memory;
  pr_fun   : EcPath.xpath;
  pr_args  : form;
  pr_event : form;
}

(*-------------------------------------------------------------------- *)
let qt_equal : quantif -> quantif -> bool = (==)
let qt_hash  : quantif -> int = Hashtbl.hash

(*-------------------------------------------------------------------- *)
let gty_equal ty1 ty2 =
  match ty1, ty2 with
  | GTty ty1, GTty ty2 ->
      EcTypes.ty_equal ty1 ty2

  | GTmodty (p1, r1), GTmodty (p2, r2)  ->
    EcModules.mty_equal p1 p2 && mr_equal r1 r2

  | GTmem mt1, GTmem mt2 ->
      EcMemory.mt_equal mt1 mt2

  | _ , _ -> false

let gty_hash = function
  | GTty ty -> EcTypes.ty_hash ty
  | GTmodty (p, _)  ->  EcModules.mty_hash p
  | GTmem _ -> 1

let gty_fv = function
  | GTty ty -> ty.ty_fv
  | GTmodty(_, (rx,r)) ->
    let fv =
      EcPath.Sm.fold (fun mp fv -> EcPath.m_fv fv mp) r EcIdent.Mid.empty in
    EcPath.Sx.fold (fun xp fv -> EcPath.x_fv fv xp) rx fv
  | GTmem mt -> EcMemory.mt_fv mt

let gtty (ty : EcTypes.ty) =
  GTty ty

let gtmodty (mt : module_type) (mr : mod_restr) =
  GTmodty (mt, mr)

let gtmem (mt : EcMemory.memtype) =
  GTmem mt

(*-------------------------------------------------------------------- *)
let b_equal (b1 : bindings) (b2 : bindings) =
  let b1_equal (x1, ty1) (x2, ty2) =
    EcIdent.id_equal x1 x2 && gty_equal ty1 ty2
  in
    List.all2 b1_equal b1 b2

let b_hash (bs : bindings) =
  let b1_hash (x, ty) =
    Why3.Hashcons.combine (EcIdent.tag x) (gty_hash ty)
  in
    Why3.Hashcons.combine_list b1_hash 0 bs

(* -------------------------------------------------------------------- *)
let hcmp_hash : hoarecmp -> int = Hashtbl.hash

(*-------------------------------------------------------------------- *)
let f_equal : form -> form -> bool = (==)
let f_compare f1 f2 = f2.f_tag - f1.f_tag
let f_hash f = f.f_tag
let f_fv f = f.f_fv
let f_ty f = f.f_ty

module MSHf = EcMaps.MakeMSH(struct
  type t = form
  let tag f = f.f_tag
end)

module Mf = MSHf.M
module Sf = MSHf.S
module Hf = MSHf.H

let hf_equal hf1 hf2 =
     f_equal hf1.hf_pr hf2.hf_pr
  && f_equal hf1.hf_po hf2.hf_po
  && EcPath.x_equal hf1.hf_f hf2.hf_f

let hs_equal hs1 hs2 =
     f_equal hs1.hs_pr hs2.hs_pr
  && f_equal hs1.hs_po hs2.hs_po
  && s_equal hs1.hs_s hs2.hs_s
  && EcMemory.me_equal hs1.hs_m hs2.hs_m

let bhf_equal bhf1 bhf2 =
     f_equal bhf1.bhf_pr bhf2.bhf_pr
  && f_equal bhf1.bhf_po bhf2.bhf_po
  && EcPath.x_equal bhf1.bhf_f bhf2.bhf_f
  && bhf1.bhf_cmp = bhf2.bhf_cmp
  && f_equal bhf1.bhf_bd bhf2.bhf_bd

let bhs_equal bhs1 bhs2 =
     f_equal bhs1.bhs_pr bhs2.bhs_pr
  && f_equal bhs1.bhs_po bhs2.bhs_po
  && s_equal bhs1.bhs_s bhs2.bhs_s
  && EcMemory.me_equal bhs1.bhs_m bhs2.bhs_m
  && bhs1.bhs_cmp = bhs2.bhs_cmp
  && f_equal bhs1.bhs_bd bhs2.bhs_bd

let eqf_equal ef1 ef2 =
     f_equal ef1.ef_pr ef2.ef_pr
  && f_equal ef1.ef_po ef2.ef_po
  && EcPath.x_equal ef1.ef_fl ef2.ef_fl
  && EcPath.x_equal ef1.ef_fr ef2.ef_fr

let eqs_equal es1 es2 =
     f_equal es1.es_pr es2.es_pr
  && f_equal es1.es_po es2.es_po
  && s_equal es1.es_sl es2.es_sl
  && s_equal es1.es_sr es2.es_sr
  && EcMemory.me_equal es1.es_ml es2.es_ml
  && EcMemory.me_equal es1.es_mr es2.es_mr

let egf_equal eg1 eg2 =
     f_equal eg1.eg_pr eg2.eg_pr
  && f_equal eg1.eg_po eg2.eg_po
  && EcModules.s_equal eg1.eg_sl eg2.eg_sl
  && EcPath.x_equal eg1.eg_fl eg2.eg_fl
  && EcPath.x_equal eg1.eg_fr eg2.eg_fr
  && EcModules.s_equal eg1.eg_sr eg2.eg_sr

let pr_equal pr1 pr2 =
     EcIdent.id_equal pr1.pr_mem pr2.pr_mem
  && EcPath.x_equal   pr1.pr_fun pr2.pr_fun
  && f_equal          pr1.pr_event pr2.pr_event
  && f_equal          pr1.pr_args pr2.pr_args

(* -------------------------------------------------------------------- *)
let hf_hash hf =
  Why3.Hashcons.combine2
    (f_hash hf.hf_pr) (f_hash hf.hf_po) (EcPath.x_hash hf.hf_f)

let hs_hash hs =
  Why3.Hashcons.combine2
    (f_hash hs.hs_pr) (f_hash hs.hs_po) (EcModules.s_hash hs.hs_s)

let bhf_hash bhf =
  Why3.Hashcons.combine_list f_hash
    (Why3.Hashcons.combine (hcmp_hash bhf.bhf_cmp) (EcPath.x_hash bhf.bhf_f))
    [bhf.bhf_pr;bhf.bhf_po;bhf.bhf_bd]

let bhs_hash bhs =
  Why3.Hashcons.combine_list f_hash
    (Why3.Hashcons.combine (hcmp_hash bhs.bhs_cmp) (EcModules.s_hash bhs.bhs_s))
    [bhs.bhs_pr;bhs.bhs_po;bhs.bhs_bd]

let ef_hash ef =
  Why3.Hashcons.combine3
    (f_hash ef.ef_pr) (f_hash ef.ef_po)
    (EcPath.x_hash ef.ef_fl) (EcPath.x_hash ef.ef_fr)

let es_hash es =
  Why3.Hashcons.combine3
    (f_hash es.es_pr) (f_hash es.es_po)
    (EcModules.s_hash es.es_sl) (EcModules.s_hash es.es_sr)

let eg_hash eg =
  Why3.Hashcons.combine3
    (f_hash eg.eg_pr) (f_hash eg.eg_po)
    (Why3.Hashcons.combine (EcModules.s_hash eg.eg_sl) (EcPath.x_hash eg.eg_fl))
    (Why3.Hashcons.combine (EcModules.s_hash eg.eg_sr) (EcPath.x_hash eg.eg_fr))

let pr_hash pr =
  Why3.Hashcons.combine3
    (EcIdent.id_hash pr.pr_mem)
    (EcPath.x_hash   pr.pr_fun)
    (f_hash          pr.pr_args)
    (f_hash          pr.pr_event)


(* -------------------------------------------------------------------- *)
module Hsform = Why3.Hashcons.Make (struct
  type t = form

  let equal_node f1 f2 =
    match f1, f2 with
    | Fquant(q1,b1,f1), Fquant(q2,b2,f2) ->
        qt_equal q1 q2 && b_equal b1 b2 && f_equal f1 f2

    | Fif(b1,t1,f1), Fif(b2,t2,f2) ->
        f_equal b1 b2 && f_equal t1 t2 && f_equal f1 f2

    | Flet(lp1,e1,f1), Flet(lp2,e2,f2) ->
        lp_equal lp1 lp2 && f_equal e1 e2 && f_equal f1 f2

    | Fint i1, Fint i2 ->
        BI.equal i1 i2

    | Flocal id1, Flocal id2 ->
        EcIdent.id_equal id1 id2

    | Fpvar(pv1,s1), Fpvar(pv2,s2) ->
        EcIdent.id_equal s1 s2 && EcTypes.pv_equal pv1 pv2

    | Fglob(mp1,m1), Fglob(mp2,m2) ->
      EcPath.m_equal mp1 mp2 && EcIdent.id_equal m1 m2

    | Fop(p1,lty1), Fop(p2,lty2) ->
        EcPath.p_equal p1 p2 && List.all2 ty_equal lty1 lty2

    | Fapp(f1,args1), Fapp(f2,args2) ->
        f_equal f1 f2 && List.all2 f_equal args1 args2

    | Ftuple args1, Ftuple args2 ->
        List.all2 f_equal args1 args2

    | Fproj(f1,i1), Fproj(f2,i2) ->
      i1 = i2 && f_equal f1 f2

    | FhoareF   hf1 , FhoareF   hf2  -> hf_equal hf1 hf2
    | FhoareS   hs1 , FhoareS   hs2  -> hs_equal hs1 hs2
    | FbdHoareF bhf1, FbdHoareF bhf2 -> bhf_equal bhf1 bhf2
    | FbdHoareS bhs1, FbdHoareS bhs2 -> bhs_equal bhs1 bhs2
    | FequivF   eqf1, FequivF   eqf2 -> eqf_equal eqf1 eqf2
    | FequivS   eqs1, FequivS   eqs2 -> eqs_equal eqs1 eqs2
    | FeagerF   eg1 , FeagerF   eg2  -> egf_equal eg1 eg2
    | Fpr       pr1 , Fpr       pr2  -> pr_equal pr1 pr2

    | _, _ -> false

  let equal f1 f2 =
       ty_equal f1.f_ty f2.f_ty
    && equal_node f1.f_node f2.f_node

  let hash f =
    match f.f_node with
    | Fquant(q, b, f) ->
        Why3.Hashcons.combine2 (f_hash f) (b_hash b) (qt_hash q)

    | Fif(b, t, f) ->
        Why3.Hashcons.combine2 (f_hash b) (f_hash t) (f_hash f)

    | Flet(lp, e, f) ->
        Why3.Hashcons.combine2 (lp_hash lp) (f_hash e) (f_hash f)

    | Fint i -> Hashtbl.hash i

    | Flocal id -> EcIdent.tag id

    | Fpvar(pv, m) ->
        Why3.Hashcons.combine (EcTypes.pv_hash pv) (EcIdent.id_hash m)

    | Fglob(mp, m) ->
        Why3.Hashcons.combine (EcPath.m_hash mp) (EcIdent.id_hash m)

    | Fop(p, lty) ->
        Why3.Hashcons.combine_list ty_hash (EcPath.p_hash p) lty

    | Fapp(f, args) ->
        Why3.Hashcons.combine_list f_hash (f_hash f) args

    | Ftuple args ->
        Why3.Hashcons.combine_list f_hash 0 args
    | Fproj(f,i) ->
        Why3.Hashcons.combine (f_hash f) i

    | FhoareF   hf  -> hf_hash hf
    | FhoareS   hs  -> hs_hash hs
    | FbdHoareF bhf -> bhf_hash bhf
    | FbdHoareS bhs -> bhs_hash bhs
    | FequivF   ef  -> ef_hash ef
    | FequivS   es  -> es_hash es
    | FeagerF   eg  -> eg_hash eg
    | Fpr       pr  -> pr_hash pr

  let fv_mlr = Sid.add mleft (Sid.singleton mright)

  let fv_node f =
    let union ex nodes =
      List.fold_left (fun s a -> fv_union s (ex a)) Mid.empty nodes
    in

    match f with
    | Fint _           -> Mid.empty
    | Fop (_, tys)     -> union (fun a -> a.ty_fv) tys
    | Fpvar (pv,m)     -> EcPath.x_fv (fv_add m Mid.empty) pv.pv_name
    | Fglob (mp,m)     -> EcPath.m_fv (fv_add m Mid.empty) mp
    | Flocal id        -> fv_singleton id
    | Fapp (f, args)   -> union f_fv (f :: args)
    | Ftuple args      -> union f_fv args
    | Fproj(e,_)       -> f_fv e
    | Fif (f1, f2, f3) -> union f_fv [f1; f2; f3]

    | Fquant(_, b, f) ->
      let do1 (id, ty) fv = fv_union (gty_fv ty) (Mid.remove id fv) in
      List.fold_right do1 b (f_fv f)

    | Flet(lp, f1, f2) ->
      let fv2 = fv_diff (f_fv f2) (lp_fv lp) in
      fv_union (f_fv f1) fv2

    | FhoareF hf ->
      let fv = fv_union (f_fv hf.hf_pr) (f_fv hf.hf_po) in
      EcPath.x_fv (Mid.remove mhr fv) hf.hf_f

    | FhoareS hs ->
      let fv = fv_union (f_fv hs.hs_pr) (f_fv hs.hs_po) in
      fv_union (EcModules.s_fv hs.hs_s) (Mid.remove (fst hs.hs_m) fv)

    | FbdHoareF bhf ->
      let fv =
        fv_union (f_fv bhf.bhf_pr)
          (fv_union (f_fv bhf.bhf_po) (f_fv bhf.bhf_bd)) in
      EcPath.x_fv (Mid.remove mhr fv) bhf.bhf_f

    | FbdHoareS bhs ->
      let fv =
        fv_union (f_fv bhs.bhs_pr)
          (fv_union (f_fv bhs.bhs_po) (f_fv bhs.bhs_bd)) in
      fv_union (EcModules.s_fv bhs.bhs_s) (Mid.remove (fst bhs.bhs_m) fv)

    | FequivF ef ->
        let fv = fv_union (f_fv ef.ef_pr) (f_fv ef.ef_po) in
        let fv = fv_diff fv fv_mlr in
        EcPath.x_fv (EcPath.x_fv fv ef.ef_fl) ef.ef_fr

    | FequivS es ->
        let fv = fv_union (f_fv es.es_pr) (f_fv es.es_po) in
        let ml, mr = fst es.es_ml, fst es.es_mr in
        let fv = fv_diff fv (Sid.add ml (Sid.singleton mr)) in
        fv_union fv
          (fv_union (EcModules.s_fv es.es_sl) (EcModules.s_fv es.es_sr))

    | FeagerF eg ->
        let fv = fv_union (f_fv eg.eg_pr) (f_fv eg.eg_po) in
        let fv = fv_diff fv fv_mlr in
        let fv = EcPath.x_fv (EcPath.x_fv fv eg.eg_fl) eg.eg_fr in
        fv_union fv
          (fv_union (EcModules.s_fv eg.eg_sl) (EcModules.s_fv eg.eg_sr))

    | Fpr pr ->
        let fve = Mid.remove mhr (f_fv pr.pr_event) in
        let fv  = EcPath.x_fv fve pr.pr_fun in
        fv_union (f_fv pr.pr_args) (fv_add pr.pr_mem fv)

  let tag n f =
    let fv = fv_union (fv_node f.f_node) f.f_ty.ty_fv in
      { f with f_tag = n; f_fv = fv; }
end)

(* -------------------------------------------------------------------- *)
let gty_as_ty =
  function GTty ty -> ty | _ -> assert false

let gty_as_mem =
  function GTmem m -> m  | _ -> assert false

let gty_as_mod =
  function GTmodty (mt, mr) -> (mt, mr) | _ -> assert false

let kind_of_gty = function
  | GTty    _ -> `Form
  | GTmem   _ -> `Mem
  | GTmodty _ -> `Mod

(* -------------------------------------------------------------------- *)
let hoarecmp_opp cmp =
  match cmp with
  | FHle -> FHge
  | FHeq -> FHeq
  | FHge -> FHle

(* -------------------------------------------------------------------- *)
let mk_form node ty =
  let aout =
    Hsform.hashcons
      { f_node = node;
        f_ty   = ty;
        f_fv   = Mid.empty;
        f_tag  = -1; }
  in assert (EcTypes.ty_equal ty aout.f_ty); aout

let f_node { f_node = form } = form

(* -------------------------------------------------------------------- *)
let f_op x tys ty = mk_form (Fop (x, tys)) ty

let f_app f args ty =
  let f, args' =
    match f.f_node with
    | Fapp (f, args') -> (f, args')
    | _ -> (f, [])
  in let args' = args' @ args in

  if List.is_empty args' then begin
    (*if ty_equal ty f.f_ty then f else mk_form f.f_node ty *) f
  end else mk_form (Fapp (f, args')) ty

(* -------------------------------------------------------------------- *)
let f_local  x ty   = mk_form (Flocal x) ty
let f_pvar   x ty m = mk_form (Fpvar(x, m)) ty
let f_pvarg  f ty m = f_pvar (pv_arg f) ty m
let f_pvloc  f v  m = f_pvar (EcTypes.pv_loc f v.v_name) v.v_type m
let f_pvlocs f vs m = List.map (fun v -> f_pvloc f v m) vs
let f_glob   mp m   = mk_form (Fglob (mp, m)) (tglob mp)

(* -------------------------------------------------------------------- *)
let f_tt     = f_op EcCoreLib.CI_Unit.p_tt    [] tunit
let f_true   = f_op EcCoreLib.CI_Bool.p_true  [] tbool
let f_false  = f_op EcCoreLib.CI_Bool.p_false [] tbool
let f_bool   = fun b -> if b then f_true else f_false

(* -------------------------------------------------------------------- *)
let f_tuple args =
  match args with
  | []  -> f_tt
  | [x] -> x
  | _   -> mk_form (Ftuple args) (ttuple (List.map f_ty args))

let f_quant q b f =
  if List.is_empty b then f else
    let (q, b, f) =
      match f.f_node with
      | Fquant(q',b',f') when q = q' -> (q, b@b', f')
      | _ -> q, b , f in
    let ty =
      if   q = Llambda
      then toarrow (List.map (fun (_,gty) -> gty_as_ty gty) b) f.f_ty
      else tbool in

    mk_form (Fquant (q, b, f)) ty

let f_proj   f  i  ty = mk_form (Fproj(f, i)) ty
let f_if     f1 f2 f3 = mk_form (Fif (f1, f2, f3)) f2.f_ty
let f_let    q  f1 f2 = mk_form (Flet (q, f1, f2)) f2.f_ty (* FIXME rename binding *)
let f_let1   x  f1 f2 = f_let (LSymbol (x, f1.f_ty)) f1 f2
let f_exists b  f     = f_quant Lexists b f
let f_forall b  f     = f_quant Lforall b f
let f_lambda b  f     = f_quant Llambda b f

let f_forall_mems bds f =
  f_forall (List.map (fun (m, mt) -> (m, GTmem mt)) bds) f

(* -------------------------------------------------------------------- *)
let ty_fbool1 = toarrow (List.make 1 tbool) tbool
let ty_fbool2 = toarrow (List.make 2 tbool) tbool

let fop_not  = f_op EcCoreLib.CI_Bool.p_not  [] ty_fbool1
let fop_and  = f_op EcCoreLib.CI_Bool.p_and  [] ty_fbool2
let fop_anda = f_op EcCoreLib.CI_Bool.p_anda [] ty_fbool2
let fop_or   = f_op EcCoreLib.CI_Bool.p_or   [] ty_fbool2
let fop_ora  = f_op EcCoreLib.CI_Bool.p_ora  [] ty_fbool2
let fop_imp  = f_op EcCoreLib.CI_Bool.p_imp  [] ty_fbool2
let fop_iff  = f_op EcCoreLib.CI_Bool.p_iff  [] ty_fbool2

let f_not  f     = f_app fop_not  [f]      tbool
let f_and  f1 f2 = f_app fop_and  [f1; f2] tbool
let f_anda f1 f2 = f_app fop_anda [f1; f2] tbool
let f_or   f1 f2 = f_app fop_or   [f1; f2] tbool
let f_ora  f1 f2 = f_app fop_ora  [f1; f2] tbool
let f_imp  f1 f2 = f_app fop_imp  [f1; f2] tbool
let f_iff  f1 f2 = f_app fop_iff  [f1; f2] tbool

let f_ands fs =
  match List.rev fs with
  | [] -> f_true
  | f::fs -> List.fold_left ((^~) f_and) f fs

let f_andas fs =
  match List.rev fs with
  | [] -> f_true
  | f::fs -> List.fold_left ((^~) f_anda) f fs

let f_ors fs =
  match List.rev fs with
  | [] -> f_false
  | f::fs -> List.fold_left ((^~) f_or) f fs

let f_oras fs =
  match List.rev fs with
  | [] -> f_false
  | f::fs -> List.fold_left ((^~) f_ora) f fs

let f_imps = List.fold_right f_imp

(* -------------------------------------------------------------------- *)
let fop_eq ty = f_op EcCoreLib.CI_Bool.p_eq [ty] (toarrow [ty; ty] tbool)

let f_eq f1 f2 = f_app (fop_eq f1.f_ty) [f1; f2] tbool

let f_eqs fs1 fs2 =
  assert (List.length fs1 = List.length fs2);
  f_ands (List.map2 f_eq fs1 fs2)

(* -------------------------------------------------------------------- *)
let f_hoareS_r hs = mk_form (FhoareS hs) tbool
let f_hoareF_r hf = mk_form (FhoareF hf) tbool

let f_hoareS hs_m hs_pr hs_s hs_po =
  f_hoareS_r { hs_m; hs_pr; hs_s; hs_po; }

let f_hoareF hf_pr hf_f hf_po =
  f_hoareF_r { hf_pr; hf_f; hf_po; }

(* -------------------------------------------------------------------- *)
let f_bdHoareS_r bhs = mk_form (FbdHoareS bhs) tbool
let f_bdHoareF_r bhf = mk_form (FbdHoareF bhf) tbool

let f_bdHoareS bhs_m bhs_pr bhs_s bhs_po bhs_cmp bhs_bd =
  f_bdHoareS_r
    { bhs_m; bhs_pr; bhs_s; bhs_po; bhs_cmp; bhs_bd; }

let f_bdHoareF bhf_pr bhf_f bhf_po bhf_cmp bhf_bd =
  f_bdHoareF_r { bhf_pr; bhf_f; bhf_po; bhf_cmp; bhf_bd; }

(* -------------------------------------------------------------------- *)
let f_equivS_r es = mk_form (FequivS es) tbool
let f_equivF_r ef = mk_form (FequivF ef) tbool

let f_equivS es_ml es_mr es_pr es_sl es_sr es_po =
   f_equivS_r { es_ml; es_mr; es_pr; es_sl; es_sr; es_po; }

let f_equivF ef_pr ef_fl ef_fr ef_po =
  f_equivF_r{ ef_pr; ef_fl; ef_fr; ef_po; }

(* -------------------------------------------------------------------- *)
let f_eagerF_r eg = mk_form (FeagerF eg) tbool

let f_eagerF eg_pr eg_sl eg_fl eg_fr eg_sr eg_po =
  f_eagerF_r { eg_pr; eg_sl; eg_fl; eg_fr; eg_sr; eg_po; }

(* -------------------------------------------------------------------- *)
let f_pr_r pr = mk_form (Fpr pr) treal

let f_pr pr_mem pr_fun pr_args pr_event =
  f_pr_r { pr_mem; pr_fun; pr_args; pr_event; }

(* -------------------------------------------------------------------- *)
let fop_int_opp = f_op EcCoreLib.CI_Int.p_int_opp [] (toarrow [tint]       tint)
let fop_int_add = f_op EcCoreLib.CI_Int.p_int_add [] (toarrow [tint; tint] tint)
let fop_int_sub = f_op EcCoreLib.CI_Int.p_int_sub [] (toarrow [tint; tint] tint)
let fop_int_mul = f_op EcCoreLib.CI_Int.p_int_mul [] (toarrow [tint; tint] tint)
let fop_int_pow = f_op EcCoreLib.CI_Int.p_int_pow [] (toarrow [tint; tint] tint)

let f_int_opp f     = f_app fop_int_opp [f]      tint
let f_int_add f1 f2 = f_app fop_int_add [f1; f2] tint
let f_int_sub f1 f2 = f_app fop_int_sub [f1; f2] tint
let f_int_mul f1 f2 = f_app fop_int_mul [f1; f2] tint
let f_int_pow f1 f2 = f_app fop_int_pow [f1; f2] tint
  
let rec f_int (n : BI.zint) =
  match BI.sign n with
  | s when 0 <= s -> mk_form (Fint n) tint
  | _             -> f_int_opp (f_int (~^ n))

let f_i0 = f_int BI.zero
let f_i1 = f_int BI.one

(* -------------------------------------------------------------------- *)
module FSmart = struct
  type a_local = EcIdent.t * ty
  type a_pvar  = prog_var * ty * memory
  type a_quant = quantif * bindings * form
  type a_if    = form tuple3
  type a_let   = lpattern * form * form
  type a_op    = EcPath.path * ty list * ty
  type a_tuple = form list
  type a_app   = form * form list * ty
  type a_proj  = form * ty
  type a_glob  = EcPath.mpath * memory

  let f_local (fp, (x, ty)) (x', ty') =
    if   x == x' && ty == ty'
    then fp
    else f_local x' ty'

  let f_pvar (fp, (pv, ty, m)) (pv', ty', m') =
    if   pv == pv' && ty == ty' && m == m'
    then fp
    else f_pvar pv' ty' m'

  let f_quant (fp, (q, b, f)) (q', b', f') =
    if   q == q' && b == b' && f == f'
    then fp
    else f_quant q' b' f'

  let f_glob (fp, (mp, m)) (mp', m') =
    if   mp == mp' && m == m'
    then fp
    else f_glob mp' m'

  let f_if (fp, (c, f1, f2)) (c', f1', f2') =
    if   c == c' && f1 == f1' && f2 == f2'
    then fp
    else f_if c' f1' f2'

  let f_let (fp, (lp, f1, f2)) (lp', f1', f2') =
    if   lp == lp' && f1 == f1' && f2 == f2'
    then fp
    else f_let lp' f1' f2'

  let f_op (fp, (op, tys, ty)) (op', tys', ty') =
    if   op == op' && tys == tys' && ty == ty'
    then fp
    else f_op op' tys' ty'

  let f_app (fp, (f, fs, ty)) (f', fs', ty') =
    if   f == f' && fs == fs' && ty == ty'
    then fp
    else f_app f' fs' ty'

  let f_tuple (fp, fs) fs' =
    if fs == fs' then fp else f_tuple fs'

  let f_proj (fp, (f, ty)) (f', ty') i =
    if   f == f' && ty == ty'
    then fp
    else f_proj f' i ty'

  let f_equivF (fp, ef) ef' =
    if eqf_equal ef ef' then fp else mk_form (FequivF ef') fp.f_ty

  let f_equivS (fp, es) es' =
    if eqs_equal es es' then fp else f_equivS_r es'

  let f_eagerF (fp, eg) eg' =
    if egf_equal eg eg' then fp else mk_form (FeagerF eg') fp.f_ty

  let f_hoareF (fp, hf) hf' =
    if hf_equal hf hf' then fp else mk_form (FhoareF hf') fp.f_ty

  let f_hoareS (fp, hs) hs' =
    if hs_equal hs hs' then fp else f_hoareS_r hs'

  let f_bdHoareF (fp, bhf) bhf' =
    if bhf_equal bhf bhf' then fp else mk_form (FbdHoareF bhf') fp.f_ty

  let f_bdHoareS (fp, bhs) bhs' =
    if bhs_equal bhs bhs' then fp else f_bdHoareS_r bhs'

  let f_pr (fp, pr) pr' =
    if pr_equal pr pr' then fp else f_pr_r pr'
end

(* -------------------------------------------------------------------- *)
let f_map gt g fp =
  match fp.f_node with
  | Fquant(q, b, f) ->
      let map_gty ((x, gty) as b1) =
        let gty' =
          match gty with
          | GTty ty ->
              let ty' = gt ty in if ty == ty' then gty else GTty ty'
          | _ -> gty
        in
          if gty == gty' then b1 else (x, gty')
      in

      let b' = List.Smart.map map_gty b in
      let f' = g f in

      FSmart.f_quant (fp, (q, b, f)) (q, b', f')

  | Fint  _ -> fp
  | Fglob _ -> fp

  | Fif (f1, f2, f3) ->
      FSmart.f_if (fp, (f1, f2, f3)) (g f1, g f2, g f3)

  | Flet (lp, f1, f2) ->
      FSmart.f_let (fp, (lp, f1, f2)) (lp, g f1, g f2)

  | Flocal id ->
      let ty' = gt fp.f_ty in
        FSmart.f_local (fp, (id, fp.f_ty)) (id, ty')

  | Fpvar (id, s) ->
      let ty' = gt fp.f_ty in
        FSmart.f_pvar (fp, (id, fp.f_ty, s)) (id, ty', s)

  | Fop (p, tys) ->
      let tys' = List.Smart.map gt tys in
      let ty'  = gt fp.f_ty in
        FSmart.f_op (fp, (p, tys, fp.f_ty)) (p, tys', ty')

  | Fapp (f, fs) ->
      let f'  = g f in
      let fs' = List.Smart.map g fs in
      let ty' = gt fp.f_ty in
        FSmart.f_app (fp, (f, fs, fp.f_ty)) (f', fs', ty')

  | Ftuple fs ->
      let fs' = List.Smart.map g fs in
        FSmart.f_tuple (fp, fs) fs'

  | Fproj (f, i) ->
      let f'  = g f in
      let ty' = gt fp.f_ty in
        FSmart.f_proj (fp, (f, fp.f_ty)) (f', ty') i

  | FhoareF hf ->
      let pr' = g hf.hf_pr in
      let po' = g hf.hf_po in
        FSmart.f_hoareF (fp, hf)
          { hf with hf_pr = pr'; hf_po = po'; }

  | FhoareS hs ->
      let pr' = g hs.hs_pr in
      let po' = g hs.hs_po in
        FSmart.f_hoareS (fp, hs)
          { hs with hs_pr = pr'; hs_po = po'; }

  | FbdHoareF bhf ->
      let pr' = g bhf.bhf_pr in
      let po' = g bhf.bhf_po in
      let bd' = g bhf.bhf_bd in
        FSmart.f_bdHoareF (fp, bhf)
          { bhf with bhf_pr = pr'; bhf_po = po'; bhf_bd = bd'; }

  | FbdHoareS bhs ->
      let pr' = g bhs.bhs_pr in
      let po' = g bhs.bhs_po in
      let bd' = g bhs.bhs_bd in
        FSmart.f_bdHoareS (fp, bhs)
          { bhs with bhs_pr = pr'; bhs_po = po'; bhs_bd = bd'; }

  | FequivF ef ->
      let pr' = g ef.ef_pr in
      let po' = g ef.ef_po in
        FSmart.f_equivF (fp, ef)
          { ef with ef_pr = pr'; ef_po = po'; }

  | FequivS es ->
      let pr' = g es.es_pr in
      let po' = g es.es_po in
        FSmart.f_equivS (fp, es)
          { es with es_pr = pr'; es_po = po'; }

  | FeagerF eg ->
      let pr' = g eg.eg_pr in
      let po' = g eg.eg_po in
        FSmart.f_eagerF (fp, eg)
          { eg with eg_pr = pr'; eg_po = po'; }

  | Fpr pr ->
      let args' = g pr.pr_args in
      let ev'   = g pr.pr_event in
        FSmart.f_pr (fp, pr) 
          { pr with pr_args = args'; pr_event = ev'; }

(* -------------------------------------------------------------------- *)
let f_iter g f =
  match f.f_node with
  | Fint     _
  | Flocal   _
  | Fpvar    _
  | Fglob    _ 
  | Fop      _ -> ()

  | Fquant   (_ , _ , f1) -> g f1
  | Fif      (f1, f2, f3) -> g f1;g f2; g f3
  | Flet     (_, f1, f2)  -> g f1;g f2
  | Fapp     (e, es)      -> List.iter g (e :: es)
  | Ftuple   es           -> List.iter g es
  | Fproj    (e, _)       -> g e

  | FhoareF   hf  -> g hf.hf_pr; g hf.hf_po
  | FhoareS   hs  -> g hs.hs_pr; g hs.hs_po
  | FbdHoareF bhf -> g bhf.bhf_pr; g bhf.bhf_po
  | FbdHoareS bhs -> g bhs.bhs_pr; g bhs.bhs_po
  | FequivF   ef  -> g ef.ef_pr; g ef.ef_po
  | FequivS   es  -> g es.es_pr; g es.es_po
  | FeagerF   eg  -> g eg.eg_pr; g eg.eg_po
  | Fpr       pr  -> g pr.pr_args; g pr.pr_event

(* -------------------------------------------------------------------- *)
let form_exists g f =
  match f.f_node with
  | Fint     _
  | Flocal   _
  | Fpvar    _
  | Fglob    _ 
  | Fop      _ -> false

  | Fquant   (_ , _ , f1) -> g f1
  | Fif      (f1, f2, f3) -> g f1 || g f2 || g f3
  | Flet     (_, f1, f2)  -> g f1 || g f2
  | Fapp     (e, es)      -> List.exists g (e :: es)
  | Ftuple   es           -> List.exists g es
  | Fproj    (e, _)       -> g e

  | FhoareF   hf  -> g hf.hf_pr   || g hf.hf_po
  | FhoareS   hs  -> g hs.hs_pr   || g hs.hs_po
  | FbdHoareF bhf -> g bhf.bhf_pr || g bhf.bhf_po
  | FbdHoareS bhs -> g bhs.bhs_pr || g bhs.bhs_po
  | FequivF   ef  -> g ef.ef_pr   || g ef.ef_po
  | FequivS   es  -> g es.es_pr   || g es.es_po
  | FeagerF   eg  -> g eg.eg_pr   || g eg.eg_po
  | Fpr       pr  -> g pr.pr_args || g pr.pr_event

(* -------------------------------------------------------------------- *)
let form_forall g f =
  match f.f_node with
  | Fint     _
  | Flocal   _
  | Fpvar    _
  | Fglob    _ 
  | Fop      _ -> true

  | Fquant   (_ , _ , f1) -> g f1
  | Fif      (f1, f2, f3) -> g f1 && g f2 && g f3
  | Flet     (_, f1, f2)  -> g f1 && g f2
  | Fapp     (e, es)      -> List.for_all g (e :: es)
  | Ftuple   es           -> List.for_all g es
  | Fproj    (e, _)       -> g e

  | FhoareF   hf  -> g hf.hf_pr   && g hf.hf_po
  | FhoareS   hs  -> g hs.hs_pr   && g hs.hs_po
  | FbdHoareF bhf -> g bhf.bhf_pr && g bhf.bhf_po
  | FbdHoareS bhs -> g bhs.bhs_pr && g bhs.bhs_po
  | FequivF   ef  -> g ef.ef_pr   && g ef.ef_po
  | FequivS   es  -> g es.es_pr   && g es.es_po
  | FeagerF   eg  -> g eg.eg_pr   && g eg.eg_po
  | Fpr       pr  -> g pr.pr_args && g pr.pr_event

(* -------------------------------------------------------------------- *)
let f_ops f =
  let aout = ref EcPath.Sp.empty in
  let rec doit f = 
    match f.f_node with
    | Fop (p, _) -> aout := Sp.add p !aout
    | _ -> f_iter doit f
  in doit f; !aout

(* -------------------------------------------------------------------- *)
exception DestrError of string

let destr_error e = raise (DestrError e)

(* -------------------------------------------------------------------- *)
let destr_forall1 f =
  match f.f_node with
  | Fquant(Lforall,(x,t)::bd,p) -> x,t,f_forall bd p
  | _ -> destr_error "forall"

let destr_forall f =
  match f.f_node with
  | Fquant(Lforall,bd,p) -> bd, p
  | _ -> destr_error "forall"

let decompose_forall f =
  match f.f_node with
  | Fquant(Lforall,bd,p) -> bd, p
  | _ -> [], f

let destr_exists1 f =
  match f.f_node with
  | Fquant(Lexists,(x,t)::bd,p) -> x,t,f_exists bd p
  | _ -> destr_error "exists"

let destr_exists f =
  match f.f_node with
  | Fquant(Lexists,bd,p) -> bd, p
  | _ -> destr_error "exists"

let destr_let f = 
  match f.f_node with
  | Flet(lp, e1,e2) -> lp,e1,e2
  | _ -> destr_error "let"

let destr_let1 f =
  match f.f_node with
  | Flet(LSymbol(x,ty), e1,e2) -> x,ty,e1,e2
  | _ -> destr_error "let1"

let destr_equivS f =
  match f.f_node with
  | FequivS es -> es
  | _ -> destr_error "equivS"

let destr_equivF f =
  match f.f_node with
  | FequivF es -> es
  | _ -> destr_error "equivF"

let destr_eagerF f =
  match f.f_node with
  | FeagerF eg -> eg
  | _ -> destr_error "eagerF"

let destr_hoareS f =
  match f.f_node with
  | FhoareS es -> es
  | _ -> destr_error "hoareS"

let destr_hoareF f =
  match f.f_node with
  | FhoareF es -> es
  | _ -> destr_error "hoareF"

let destr_bdHoareS f =
  match f.f_node with
  | FbdHoareS es -> es
  | _ -> destr_error "bdHoareS"

let destr_bdHoareF f =
  match f.f_node with
  | FbdHoareF es -> es
  | _ -> destr_error "bdHoareF"

let destr_pr f =
  match f.f_node with
  | Fpr pr -> pr
  | _ -> destr_error "pr"

let destr_programS side f =
  match side, f.f_node with
  | None  , FhoareS   hs  -> (hs.hs_m, hs.hs_s)
  | None  , FbdHoareS bhs -> (bhs.bhs_m, bhs.bhs_s)
  | Some b, FequivS   es  -> begin
      match b with
      | `Left  -> (es.es_ml, es.es_sl)
      | `Right -> (es.es_mr, es.es_sr)
  end
  | _, _ -> destr_error "programS"

let destr_int f =
  match f.f_node with
  | Fint n -> n

  | Fapp (op, [{f_node = Fint n}]) when f_equal op fop_int_opp ->
      BI.neg n

  | _ -> destr_error "destr_int"

(* -------------------------------------------------------------------- *)
let is_op_and_sym  p = EcPath.p_equal EcCoreLib.CI_Bool.p_and p
let is_op_and_asym p = EcPath.p_equal EcCoreLib.CI_Bool.p_anda p
let is_op_and_any  p = is_op_and_sym p || is_op_and_asym p
let is_op_or_sym   p = EcPath.p_equal EcCoreLib.CI_Bool.p_or p
let is_op_or_asym  p = EcPath.p_equal EcCoreLib.CI_Bool.p_ora p
let is_op_or_any   p = is_op_or_sym  p || is_op_or_asym  p
let is_op_not      p = EcPath.p_equal EcCoreLib.CI_Bool.p_not p
let is_op_imp      p = EcPath.p_equal EcCoreLib.CI_Bool.p_imp p
let is_op_iff      p = EcPath.p_equal EcCoreLib.CI_Bool.p_iff p
let is_op_eq       p = EcPath.p_equal EcCoreLib.CI_Bool.p_eq  p

(* -------------------------------------------------------------------- *)
let destr_app   = function { f_node = Fapp (f, fs) } -> (f, fs) | f -> (f, [])
let destr_tuple = function { f_node = Ftuple fs } -> fs | _ -> destr_error "tuple"
let destr_local = function { f_node = Flocal id } -> id | _ -> destr_error "local"

let _destr1 ~name pred form =
  match destr_app form with
  | { f_node = Fop (p, _) }, [f] when pred p -> f
  | _ -> destr_error name

let _destr2 ~name pred form =
  match destr_app form with
  | { f_node = Fop (p, _) }, [f1; f2] when pred p -> (f1, f2)
  | _ -> destr_error name

let destr_not = _destr1 ~name:"not" is_op_not
let destr_and = _destr2 ~name:"and" is_op_and_any
let destr_or  = _destr2 ~name:"or"  is_op_or_any
let destr_imp = _destr2 ~name:"imp" is_op_imp
let destr_iff = _destr2 ~name:"iff" is_op_iff
let destr_eq  = _destr2 ~name:"eq"  is_op_eq

let destr_eq_or_iff = 
  _destr2 ~name:"eq-or-iff" (fun p -> is_op_eq p || is_op_iff p)

let destr_or_r form =
  match destr_app form with
  | { f_node = Fop (p, _) }, [f1; f2] when is_op_or_sym  p -> (`Sym , (f1, f2))
  | { f_node = Fop (p, _) }, [f1; f2] when is_op_or_asym p -> (`Asym, (f1, f2))
  | _ -> destr_error "or"

let destr_and_r form =
  match destr_app form with
  | { f_node = Fop (p, _) }, [f1; f2] when is_op_and_sym  p -> (`Sym , (f1, f2))
  | { f_node = Fop (p, _) }, [f1; f2] when is_op_and_asym p -> (`Asym, (f1, f2))
  | _ -> destr_error "and"

let destr_nots form =
  let rec aux b form = 
    match try Some (destr_not form) with DestrError _ -> None with
    | None      -> (b, form)
    | Some form -> aux (not b) form
  in aux true form

(* -------------------------------------------------------------------- *)
let is_from_destr dt f =
  try ignore (dt f); true with DestrError _ -> false

let is_true      f = f_equal f f_true
let is_false     f = f_equal f f_false
let is_tuple     f = is_from_destr destr_tuple     f
let is_local     f = is_from_destr destr_local     f
let is_and       f = is_from_destr destr_and       f
let is_or        f = is_from_destr destr_or        f
let is_not       f = is_from_destr destr_not       f
let is_imp       f = is_from_destr destr_imp       f
let is_iff       f = is_from_destr destr_iff       f
let is_eq        f = is_from_destr destr_eq        f
let is_forall    f = is_from_destr destr_forall1   f
let is_exists    f = is_from_destr destr_exists1   f
let is_let       f = is_from_destr destr_let1      f
let is_equivF    f = is_from_destr destr_equivF    f
let is_equivS    f = is_from_destr destr_equivS    f
let is_eagerF    f = is_from_destr destr_eagerF    f
let is_hoareS    f = is_from_destr destr_hoareS    f
let is_hoareF    f = is_from_destr destr_hoareF    f
let is_bdHoareS  f = is_from_destr destr_bdHoareS  f
let is_bdHoareF  f = is_from_destr destr_bdHoareF  f
let is_pr        f = is_from_destr destr_pr        f
let is_eq_or_iff f = (is_eq f) || (is_iff f)

(* -------------------------------------------------------------------- *)
let rec form_of_expr mem (e: expr) =
  match e.e_node with
  | Eint n -> f_int n
  | Elocal id -> f_local id e.e_ty
  | Evar pv -> f_pvar pv e.e_ty mem
  | Eop (op,tys) -> f_op op tys e.e_ty
  | Eapp (ef,es) -> f_app (form_of_expr mem ef) (List.map (form_of_expr mem) es) e.e_ty
  | Elet (lpt,e1,e2) -> f_let lpt (form_of_expr mem e1) (form_of_expr mem e2)
  | Etuple es -> f_tuple (List.map (form_of_expr mem) es)
  | Eproj(e1,i) -> f_proj (form_of_expr mem e1) i e.e_ty
  | Eif (e1,e2,e3) ->
      f_if (form_of_expr mem e1) (form_of_expr mem e2) (form_of_expr mem e3)
  | Elam(b,e) ->
    f_lambda (List.map (fun (x,ty) -> (x,GTty ty)) b) (form_of_expr mem e)

(* -------------------------------------------------------------------- *)
type f_subst = {
  fs_freshen : bool; (* true means freshen locals *)
  fs_mp      : EcPath.mpath Mid.t;
  fs_loc     : form Mid.t;
  fs_mem     : EcIdent.t Mid.t;
  fs_sty     : ty_subst;
  fs_ty      : ty -> ty;
  fs_opdef   : (EcIdent.t list * expr) Mp.t;
  fs_pddef   : (EcIdent.t list * form) Mp.t;
}

(* -------------------------------------------------------------------- *)
module Fsubst = struct
  let f_subst_id = {
    fs_freshen = false;
    fs_mp      = Mid.empty;
    fs_loc     = Mid.empty;
    fs_mem     = Mid.empty;
    fs_sty     = ty_subst_id;
    fs_ty      = ty_subst ty_subst_id;
    fs_opdef   = Mp.empty;
    fs_pddef   = Mp.empty
  }

  let is_subst_id s =
       s.fs_freshen = false
    && is_ty_subst_id s.fs_sty
    && Mid.is_empty   s.fs_loc
    && Mid.is_empty   s.fs_mem
    && Mp.is_empty    s.fs_opdef
    && Mp.is_empty    s.fs_pddef

  let f_subst_init ?freshen ?mods ?sty ?opdef ?prdef () =
    let sty = odfl ty_subst_id sty in
    { f_subst_id
        with fs_freshen = odfl false freshen;
             fs_mp      = odfl Mid.empty mods;
             fs_sty     = sty;
             fs_ty      = ty_subst sty;
             fs_opdef   = odfl Mp.empty opdef;
             fs_pddef   = odfl Mp.empty prdef; }

  (* ------------------------------------------------------------------ *)
  let f_bind_local s x t =
    let merger o = assert (o = None); Some t in
      { s with fs_loc = Mid.change merger x s.fs_loc }

  let f_bind_mem s m1 m2 =
    let merger o = assert (o = None); Some m2 in
      { s with fs_mem = Mid.change merger m1 s.fs_mem }

  let f_bind_mod s x mp =
    let merger o = assert (o = None); Some mp in
    let smp = Mid.change merger x s.fs_mp in
    let sty = s.fs_sty in
    let sty = { sty with ts_mp = EcPath.m_subst sty.ts_p smp } in
      { s with fs_mp = smp; fs_sty = sty; fs_ty = ty_subst sty }

  (* ------------------------------------------------------------------ *)
  let f_rem_local s x =
    { s with fs_loc = Mid.remove x s.fs_loc }

  let f_rem_mem s m =
    { s with fs_mem = Mid.remove m s.fs_mem }

  let f_rem_mod s m =
    let smp = Mid.remove m s.fs_mp in
    let sty = s.fs_sty in
    let sty = { sty with ts_mp = EcPath.m_subst sty.ts_p smp } in

    { s with fs_mp = smp; fs_sty = sty; fs_ty = ty_subst sty }

  (* ------------------------------------------------------------------ *)
  let add_local s (x,t as xt) =
    let x' = if s.fs_freshen then EcIdent.fresh x else x in
    let t' = s.fs_ty t in
      if   x == x' && t == t'
      then (s, xt)
      else f_bind_local s x (f_local x' t'), (x',t')

  let add_locals = List.Smart.map_fold add_local

  let subst_lpattern (s: f_subst) (lp:lpattern) =
    match lp with
    | LSymbol x ->
        let (s, x') = add_local s x in
          if x == x' then (s, lp) else (s, LSymbol x')

    | LTuple xs ->
        let (s, xs') = add_locals s xs in
          if xs == xs' then (s, lp) else (s, LTuple xs')

    | LRecord (p, xs) ->
        let (s, xs') =
          List.Smart.map_fold
            (fun s ((x, t) as xt) ->
              match x with
              | None ->
                  let t' = s.fs_ty t in
                    if t == t' then (s, xt) else (s, (x, t'))
              | Some x ->
                  let (s, (x', t')) = add_local s (x, t) in
                    if   x == x' && t == t'
                    then (s, xt)
                    else (s, (Some x', t')))
            s xs
        in
          if xs == xs' then (s, lp) else (s, LRecord (p, xs'))

  let gty_subst s gty =
    if is_subst_id s then gty else

    match gty with
    | GTty ty ->
        let ty' = s.fs_ty ty in
        if ty == ty' then gty else GTty ty'

    | GTmodty (p, (rx, r)) ->
        let sub  = s.fs_sty.ts_mp in
        let xsub = EcPath.x_substm s.fs_sty.ts_p s.fs_mp in
        let p'   = mty_subst s.fs_sty.ts_p sub p in
        let rx'  = Sx.fold (fun m rx' -> Sx.add (xsub m) rx') rx Sx.empty in
        let r'   = Sm.fold (fun m r' -> Sm.add (sub m) r') r Sm.empty in

        if   p == p' && Sx.equal rx rx' && Sm.equal r r'
        then gty
        else GTmodty (p', (rx', r'))

    | GTmem mt ->
        let mt' = EcMemory.mt_substm s.fs_sty.ts_p s.fs_mp s.fs_ty mt in
        if mt == mt' then gty else GTmem mt'

  (* ------------------------------------------------------------------ *)
  let add_binding s (x, gty as xt) =
    let gty' = gty_subst s gty in
    let x'   = if s.fs_freshen then EcIdent.fresh x else x in

    if   x == x' && gty == gty'
    then
      let s = match gty with
        | GTty    _ -> f_rem_local s x
        | GTmodty _ -> f_rem_mod   s x
        | GTmem   _ -> f_rem_mem   s x
      in
        (s, xt)
    else
      let s = match gty' with
        | GTty   ty -> f_bind_local s x (f_local x' ty)
        | GTmodty _ -> f_bind_mod s x (EcPath.mident x')
        | GTmem   _ -> f_bind_mem s x x'
      in
        (s, (x', gty'))

  let add_bindings = List.map_fold add_binding

  (* ------------------------------------------------------------------ *)
  let rec f_subst s fp =
    match fp.f_node with
    | Fquant (q, b, f) ->
        let s, b' = add_bindings s b in
        let f'    = f_subst s f in
          FSmart.f_quant (fp, (q, b, f)) (q, b', f')

    | Flet (lp, f1, f2) ->
        let f1'    = f_subst s f1 in
        let s, lp' = subst_lpattern s lp in
        let f2'    = f_subst s f2 in
          FSmart.f_let (fp, (lp, f1, f2)) (lp', f1', f2')

    | Flocal id -> begin
      match Mid.find_opt id s.fs_loc with
      | Some f -> f
      | None ->
          let ty' = s.fs_ty fp.f_ty in
            FSmart.f_local (fp, (id, fp.f_ty)) (id, ty')
    end

    | Fop (p, tys) when Mp.mem p s.fs_opdef ->
        let ty   = s.fs_ty fp.f_ty in
        let tys  = List.Smart.map s.fs_ty tys in
        let body = oget (Mp.find_opt p s.fs_opdef) in
          f_subst_op s.fs_freshen ty tys [] body

    | Fop (p, tys) when Mp.mem p s.fs_pddef ->
        let ty   = s.fs_ty fp.f_ty in
        let tys  = List.Smart.map s.fs_ty tys in
        let body = oget (Mp.find_opt p s.fs_pddef) in
          f_subst_pd ty tys [] body

    | Fapp ({ f_node = Fop (p, tys) }, args) when Mp.mem p s.fs_opdef ->
        let ty   = s.fs_ty fp.f_ty in
        let tys  = List.Smart.map s.fs_ty tys in
        let body = oget (Mp.find_opt p s.fs_opdef) in
          f_subst_op s.fs_freshen ty tys (List.map (f_subst s) args) body

    | Fapp ({ f_node = Fop (p, tys) }, args) when Mp.mem p s.fs_pddef ->
        let ty   = s.fs_ty fp.f_ty in
        let tys  = List.Smart.map s.fs_ty tys in
        let body = oget (Mp.find_opt p s.fs_pddef) in
          f_subst_pd ty tys (List.map (f_subst s) args) body

    | Fop (p, tys) ->
        let ty'  = s.fs_ty fp.f_ty in
        let tys' = List.Smart.map s.fs_ty tys in
        let p'   = s.fs_sty.ts_p p in
          FSmart.f_op (fp, (p, tys, fp.f_ty)) (p', tys', ty')

    | Fpvar (pv, m) ->
        let pv' = pv_subst (EcPath.x_substm s.fs_sty.ts_p s.fs_mp) pv in
        let m'  = Mid.find_def m m s.fs_mem in
        let ty' = s.fs_ty fp.f_ty in
          FSmart.f_pvar (fp, (pv, fp.f_ty, m)) (pv', ty', m')

    | Fglob (mp, m) ->
        let m'  = Mid.find_def m m s.fs_mem in
        let mp' = s.fs_sty.ts_mp mp in
          FSmart.f_glob (fp, (mp, m)) (mp', m')

    | FhoareF hf ->
        assert (not (Mid.mem mhr s.fs_mem) && not (Mid.mem mhr s.fs_mem));
        let pr' = f_subst s hf.hf_pr in
        let po' = f_subst s hf.hf_po in
        let mp' = EcPath.x_substm s.fs_sty.ts_p s.fs_mp hf.hf_f in
          FSmart.f_hoareF (fp, hf)
            { hf_pr = pr'; hf_po = po'; hf_f = mp'; }

    | FhoareS hs ->
        assert (not (Mid.mem (fst hs.hs_m) s.fs_mem));
        let es  = e_subst_init s.fs_freshen s.fs_sty.ts_p s.fs_ty s.fs_opdef s.fs_mp in
        let pr' = f_subst s hs.hs_pr in
        let po' = f_subst s hs.hs_po in
        let st' = EcModules.s_subst es hs.hs_s in
        let me' =
          EcMemory.me_substm s.fs_sty.ts_p s.fs_mp s.fs_mem s.fs_ty hs.hs_m in
        FSmart.f_hoareS (fp, hs)
          { hs_pr = pr'; hs_po = po'; hs_s = st'; hs_m = me'; }

    | FbdHoareF bhf ->
      assert (not (Mid.mem mhr s.fs_mem) && not (Mid.mem mhr s.fs_mem));
      let pr' = f_subst s bhf.bhf_pr in
      let po' = f_subst s bhf.bhf_po in
      let mp' = EcPath.x_substm s.fs_sty.ts_p s.fs_mp bhf.bhf_f in
      let bd' = f_subst s bhf.bhf_bd in
      FSmart.f_bdHoareF (fp, bhf)
        { bhf with bhf_pr = pr'; bhf_po = po'; bhf_f = mp'; bhf_bd = bd'; }

    | FbdHoareS bhs ->
      assert (not (Mid.mem (fst bhs.bhs_m) s.fs_mem));
      let es  = e_subst_init s.fs_freshen s.fs_sty.ts_p s.fs_ty s.fs_opdef s.fs_mp in
      let pr' = f_subst s bhs.bhs_pr in
      let po' = f_subst s bhs.bhs_po in
      let st' = EcModules.s_subst es bhs.bhs_s in
      let me' =
        EcMemory.me_substm s.fs_sty.ts_p s.fs_mp s.fs_mem s.fs_ty bhs.bhs_m in
      let bd' = f_subst s bhs.bhs_bd in
      FSmart.f_bdHoareS (fp, bhs)
        { bhs with bhs_pr = pr'; bhs_po = po'; bhs_s = st';
          bhs_bd = bd'; bhs_m  = me'; }

    | FequivF ef ->
      assert (not (Mid.mem mleft s.fs_mem) && not (Mid.mem mright s.fs_mem));
      let m_subst = EcPath.x_substm s.fs_sty.ts_p s.fs_mp in
      let pr' = f_subst s ef.ef_pr in
      let po' = f_subst s ef.ef_po in
      let fl' = m_subst ef.ef_fl in
      let fr' = m_subst ef.ef_fr in
      FSmart.f_equivF (fp, ef)
        { ef_pr = pr'; ef_po = po'; ef_fl = fl'; ef_fr = fr'; }

    | FequivS eqs ->
      assert (not (Mid.mem (fst eqs.es_ml) s.fs_mem) &&
                not (Mid.mem (fst eqs.es_mr) s.fs_mem));
      let es = e_subst_init s.fs_freshen s.fs_sty.ts_p s.fs_ty s.fs_opdef s.fs_mp in
      let s_subst = EcModules.s_subst es in

      let pr' = f_subst s eqs.es_pr in
      let po' = f_subst s eqs.es_po in
      let sl' = s_subst eqs.es_sl in
      let sr' = s_subst eqs.es_sr in
      let ml' =
        EcMemory.me_substm s.fs_sty.ts_p s.fs_mp s.fs_mem s.fs_ty eqs.es_ml in
      let mr' =
        EcMemory.me_substm s.fs_sty.ts_p s.fs_mp s.fs_mem s.fs_ty eqs.es_mr in

      FSmart.f_equivS (fp, eqs)
        { es_ml = ml'; es_mr = mr';
          es_pr = pr'; es_po = po';
          es_sl = sl'; es_sr = sr'; }

    | FeagerF eg ->
      assert (not (Mid.mem mleft s.fs_mem) && not (Mid.mem mright s.fs_mem));
      let m_subst = EcPath.x_substm s.fs_sty.ts_p s.fs_mp in
      let pr' = f_subst s eg.eg_pr in
      let po' = f_subst s eg.eg_po in
      let fl' = m_subst eg.eg_fl in
      let fr' = m_subst eg.eg_fr in

      let es = e_subst_init s.fs_freshen s.fs_sty.ts_p s.fs_ty s.fs_opdef s.fs_mp in
      let s_subst = EcModules.s_subst es in
      let sl' = s_subst eg.eg_sl in
      let sr' = s_subst eg.eg_sr in

      FSmart.f_eagerF (fp, eg)
        { eg_pr = pr'; eg_sl = sl';eg_fl = fl';
          eg_fr = fr'; eg_sr = sr'; eg_po = po'; }

    | Fpr pr ->
      assert (not (Mid.mem mhr s.fs_mem));
      let pr_mem   = Mid.find_def pr.pr_mem pr.pr_mem s.fs_mem in
      let pr_fun   = EcPath.x_substm s.fs_sty.ts_p s.fs_mp pr.pr_fun in
      let pr_args  = f_subst s pr.pr_args in
      let pr_event = f_subst s pr.pr_event in

      FSmart.f_pr (fp, pr) { pr_mem; pr_fun; pr_args; pr_event; }

    | _ -> f_map s.fs_ty (f_subst s) fp

  and f_subst_op freshen fty tys args (tyids, e) =
    (* FIXME: factor this out *)
    (* FIXME: is [mhr] good as a default? *)

    let e =
      let sty = Tvar.init tyids tys in
      let sty = ty_subst { ty_subst_id with ts_v = Mid.find_opt^~ sty; } in
      let sty = { e_subst_id with es_freshen = freshen; es_ty = sty ; } in
        e_subst sty e
    in

    let (sag, args, e) =
      match e.e_node with
      | Elam (largs, lbody) when args <> [] ->
          let largs1, largs2 = List.takedrop (List.length args  ) largs in
          let  args1,  args2 = List.takedrop (List.length largs1)  args in
            (Mid.of_list (List.combine (List.map fst largs1) args1),
             args2, e_lam largs2 lbody)

      | _ -> (Mid.of_list [], args, e)
    in

    let sag = { f_subst_id with fs_loc = sag } in
      f_app (f_subst sag (form_of_expr mhr e)) args fty

  and f_subst_pd fty tys args (tyids, f) =
    (* FIXME: factor this out *)
    (* FIXME: is fd_freshen value correct? *)

    let f =
      let sty = Tvar.init tyids tys in
      let sty = ty_subst { ty_subst_id with ts_v = Mid.find_opt^~ sty; } in
      let sty = { f_subst_id with
                    fs_freshen = true;
                    fs_ty      = sty ; } in
        f_subst sty f
    in

    let (sag, args, f) =
      match f.f_node with
      | Fquant (Llambda, largs, lbody) when args <> [] ->
          let largs1, largs2 = List.takedrop (List.length args  ) largs in
          let  args1,  args2 = List.takedrop (List.length largs1)  args in
            (Mid.of_list (List.combine (List.map fst largs1) args1),
             args2, f_lambda largs2 lbody)

      | _ -> (Mid.of_list [], args, f)
    in

    let sag = { f_subst_id with fs_loc = sag } in
      f_app (f_subst sag f) args fty

  (* ------------------------------------------------------------------ *)
  let f_subst_local x t =
    let s = f_bind_local f_subst_id x t in
    fun f -> if Mid.mem x f.f_fv then f_subst s f else f

  let f_subst_mem m1 m2 =
    let s = f_bind_mem f_subst_id m1 m2 in
    fun f -> if Mid.mem m1 f.f_fv then f_subst s f else f

  let f_subst_mod x mp =
    let s = f_bind_mod f_subst_id x mp in
    fun f -> if Mid.mem x f.f_fv then f_subst s f else f

  let f_subst s =
    if is_subst_id s then identity
    else f_subst s

  (* ------------------------------------------------------------------ *)
  let mapty sty =
    f_subst { f_subst_id with fs_sty = sty; fs_ty = ty_subst sty }

  let uni uidmap =
    mapty { ty_subst_id with ts_u = uidmap }

  (* ------------------------------------------------------------------ *)
  let subst_locals s =
    Hf.memo_rec 107 (fun aux f ->
      match f.f_node with
      | Flocal id ->
          (try Mid.find id s with Not_found -> f)
      | _ -> f_map (fun ty -> ty) aux f)

  let subst_local id f1 f2 =
    subst_locals (Mid.singleton id f1) f2

  (* ------------------------------------------------------------------ *)
  let init_subst_tvar s =
    let sty = { ty_subst_id with ts_v = Mid.find_opt^~ s } in
    { f_subst_id with fs_freshen = true; fs_sty = sty; fs_ty = ty_subst sty }

  let subst_tvar s =
    f_subst (init_subst_tvar s)
end

(* -------------------------------------------------------------------- *)
let can_subst f =
  match f.f_node with
  | Fint _ | Flocal _ | Fpvar _ | Fop _ -> true
  | _ -> false

(* -------------------------------------------------------------------- *)
type core_op = [
  | `True
  | `False
  | `Not
  | `And of [`Asym | `Sym]
  | `Or  of [`Asym | `Sym]
  | `Imp
  | `Iff
  | `Eq
]

let core_ops =
  let core_ops =
    [EcCoreLib.CI_Bool.p_true    , `True     ;
     EcCoreLib.CI_Bool.p_false   , `False    ;
     EcCoreLib.CI_Bool.p_not     , `Not      ;
     EcCoreLib.CI_Bool.p_anda    , `And `Asym;
     EcCoreLib.CI_Bool.p_and     , `And `Sym ;
     EcCoreLib.CI_Bool.p_ora     , `Or  `Asym;
     EcCoreLib.CI_Bool.p_or      , `Or  `Sym ;
     EcCoreLib.CI_Bool.p_imp     , `Imp      ;
     EcCoreLib.CI_Bool.p_iff     , `Iff      ;
     EcCoreLib.CI_Bool.p_eq      , `Eq       ; ]
  in

  let tbl = EcPath.Hp.create 11 in
    List.iter (fun (p, k) -> EcPath.Hp.add tbl p k) core_ops;
    tbl

let core_op_kind (p : EcPath.path) =
  EcPath.Hp.find_opt core_ops p
