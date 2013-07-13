(* -------------------------------------------------------------------- *)
open EcDebug
open EcUtils
open EcMaps
open EcIdent
open EcTypes

open EcModules

type memory = EcMemory.memory

(* -------------------------------------------------------------------- *)

type gty =
  | GTty    of EcTypes.ty
  | GTmodty of module_type * mod_restr 
  | GTmem   of EcMemory.memtype

type quantif = 
  | Lforall
  | Lexists
  | Llambda

type binding = (EcIdent.t * gty) list

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
  | Fquant  of quantif * binding * form
  | Fif     of form * form * form
  | Flet    of lpattern * form * form
  | Fint    of int
  | Flocal  of EcIdent.t
  | Fpvar   of EcTypes.prog_var * memory
  | Fglob   of EcPath.mpath     * memory
  | Fop     of EcPath.path * ty list
  | Fapp    of form * form list
  | Ftuple  of form list

  | FhoareF of hoareF (* $hr / $hr *)
  | FhoareS of hoareS 

  | FbdHoareF of bdHoareF (* $hr / $hr *)
  | FbdHoareS of bdHoareS 

  | FequivF of equivF (* $left,$right / $left,$right *)
  | FequivS of equivS 

  | Fpr of pr (* hr *)

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

and pr = memory * EcPath.xpath * form list * form

type app_bd_info =
| AppNone
| AppSingle of form
| AppMult   of (form * form * form * form * form)

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

(*-------------------------------------------------------------------- *)
let b_equal (b1 : binding) (b2 : binding) =
  let b1_equal (x1, ty1) (x2, ty2) = 
    EcIdent.id_equal x1 x2 && gty_equal ty1 ty2
  in
    List.all2 b1_equal b1 b2
    
let b_hash (bs : binding) =
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
        i1 = i2

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

    | FhoareF hf1, FhoareF hf2 -> hf_equal hf1 hf2
    | FhoareS hs1, FhoareS hs2 -> hs_equal hs1 hs2

    | FbdHoareF bhf1, FbdHoareF bhf2 -> bhf_equal bhf1 bhf2
    | FbdHoareS bhs1, FbdHoareS bhs2 -> bhs_equal bhs1 bhs2
        
    | FequivF eqf1, FequivF eqf2 -> eqf_equal eqf1 eqf2
    | FequivS eqs1, FequivS eqs2 -> eqs_equal eqs1 eqs2

    | Fpr (m1, mp1, args1, ev1), Fpr (m2, mp2, args2, ev2) ->
           EcIdent.id_equal m1  m2
        && EcPath.x_equal   mp1 mp2
        && f_equal          ev1 ev2
        && (List.all2 f_equal args1 args2)

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

    | FhoareF hf -> hf_hash hf
    | FhoareS hs -> hs_hash hs

    | FbdHoareF bhf -> bhf_hash bhf
    | FbdHoareS bhs -> bhs_hash bhs

    | FequivF ef -> ef_hash ef
    | FequivS es -> es_hash es

    | Fpr (m, mp, args, ev) ->
        let id =
          Why3.Hashcons.combine2
            (EcIdent.id_hash m)
            (EcPath.x_hash   mp)
            (f_hash          ev)
        in
          Why3.Hashcons.combine_list f_hash id args

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

    | Fpr (m,mp,args,event) ->
        let fve = Mid.remove mhr (f_fv event) in
        let fv  = EcPath.x_fv fve mp in
        List.fold_left (fun s f -> fv_union s (f_fv f)) (fv_add m fv) args
  
  let tag n f = 
    let fv = fv_union (fv_node f.f_node) f.f_ty.ty_fv in
      { f with f_tag = n; f_fv = fv; }
end)

(* -------------------------------------------------------------------- *)
let mk_form node ty =  Hsform.hashcons 
    { f_node = node;
      f_ty   = ty;
      f_fv   = Mid.empty;
      f_tag  = -1; }

let ty_bool = tbool
let ty_int  = tint 
let ty_unit = tunit
let ty_real = treal

(* -------------------------------------------------------------------- *)
let f_op x tys ty = mk_form (Fop (x, tys)) ty

let f_app f args ty =
  if args = [] then f 
  else match f.f_node with
  | Fapp(f',args') -> mk_form (Fapp(f', args'@args)) ty
  | _ -> mk_form (Fapp(f,args)) ty 

(* -------------------------------------------------------------------- *)
let f_local x ty = mk_form (Flocal x) ty

let f_pvar x ty m = mk_form (Fpvar(x, m)) ty

let f_pvloc f v m = 
  f_pvar (EcTypes.pv_loc f v.v_name) v.v_type m

let f_pvlocs f vs m =
  List.map (fun v -> f_pvloc f v m) vs

let f_glob mp m = mk_form (Fglob(mp,m)) (tglob mp)

(* -------------------------------------------------------------------- *)
let f_tuple args = 
  match args with
  | [x] -> x
  | _ -> mk_form (Ftuple args) (ttuple (List.map f_ty args))

let f_if f1 f2 f3 =
  mk_form (Fif (f1, f2, f3)) f2.f_ty 

let f_let q f1 f2 =
  mk_form (Flet (q, f1, f2)) f2.f_ty (* FIXME rename binding *)

let f_let1 x f1 f2 = f_let (LSymbol (x, f1.f_ty)) f1 f2

let destr_gty = function 
  | GTty ty -> ty 
  | _ -> assert false

let f_quant q b f = 
  if b = [] then f 
  else 
    let q, b, f = 
      match f.f_node with
      | Fquant(q',b',f') when q = q' -> q, b@b', f'
      | _ -> q, b , f in
    let ty = 
      if q = Llambda then 
        let dom = List.map (fun (_,gty) -> destr_gty gty) b in
        toarrow dom f.f_ty 
      else ty_bool in
    mk_form (Fquant(q,b,f)) ty

let f_exists b f = f_quant Lexists b f 
let f_forall b f = f_quant Lforall b f
let f_lambda b f = f_quant Llambda b f

(* -------------------------------------------------------------------- *)
let f_tt     = f_op EcCoreLib.p_tt [] ty_unit
let f_true   = f_op EcCoreLib.p_true [] ty_bool
let f_false  = f_op EcCoreLib.p_false [] ty_bool
let f_bool   = fun b -> if b then f_true else f_false

let fop_int_opp  = f_op EcCoreLib.p_int_opp [] (tfun tint tint)
let f_int_opp f = f_app fop_int_opp [f] tint

let rec f_int n  = 
  if 0 <= n then mk_form (Fint n) ty_int
  else f_int_opp (f_int (-n))

let f_i0     = f_int 0
let f_i1     = f_int 1

let f_op_real_of_int = f_op EcCoreLib.p_from_int [] (tfun ty_int ty_real)
let f_real_of_int f  = f_app f_op_real_of_int [f] ty_real
let f_rint n         = f_real_of_int (f_int n)
let f_r0             = f_rint 0
let f_r1             = f_rint 1

(* -------------------------------------------------------------------- *)
let ty_fbool1 = toarrow (List.create 1 ty_bool) ty_bool
let ty_fbool2 = toarrow (List.create 2 ty_bool) ty_bool

let fop_not  = f_op EcCoreLib.p_not  [] ty_fbool1
let fop_and  = f_op EcCoreLib.p_and  [] ty_fbool2
let fop_anda = f_op EcCoreLib.p_anda [] ty_fbool2
let fop_or   = f_op EcCoreLib.p_or   [] ty_fbool2
let fop_ora  = f_op EcCoreLib.p_ora  [] ty_fbool2
let fop_imp  = f_op EcCoreLib.p_imp  [] ty_fbool2
let fop_iff  = f_op EcCoreLib.p_iff  [] ty_fbool2

let f_not  f     = f_app fop_not  [f]      ty_bool
let f_and  f1 f2 = f_app fop_and  [f1; f2] ty_bool
let f_anda f1 f2 = f_app fop_anda [f1; f2] ty_bool
let f_or   f1 f2 = f_app fop_or   [f1; f2] ty_bool
let f_ora  f1 f2 = f_app fop_ora  [f1; f2] ty_bool
let f_imp  f1 f2 = f_app fop_imp  [f1; f2] ty_bool
let f_iff  f1 f2 = f_app fop_iff  [f1; f2] ty_bool

let f_ands fs =
  match List.rev fs with
  | [] -> f_true
  | f::fs -> List.fold_left ((^~) f_and) f fs

let f_ors fs =
  match List.rev fs with
  | [] -> f_true
  | f::fs -> List.fold_left ((^~) f_or) f fs

let f_imps = List.fold_right f_imp

(* -------------------------------------------------------------------- *)
let fop_eq = fun ty -> f_op EcCoreLib.p_eq [ty] (toarrow [ty; ty] tbool)

let f_eq f1 f2 = f_app (fop_eq f1.f_ty) [f1; f2] ty_bool

let f_eqs fs1 fs2 =
  assert (List.length fs1 = List.length fs2);
  f_ands (List.map2 f_eq fs1 fs2)

let f_eqparams f1 vs1 m1 f2 vs2 m2 =
  f_eqs (f_pvlocs f1 vs1 m1) (f_pvlocs f2 vs2 m2)

let f_eqres f1 ty1 m1 f2 ty2 m2 =
  f_eq (f_pvar (pv_res f1) ty1 m1)  (f_pvar (pv_res f2) ty2 m2)

let f_eqglob mp1 m1 mp2 m2 =  
  f_eq (f_glob mp1 m1) (f_glob mp2 m2)

(* -------------------------------------------------------------------- *)
let f_hoareS_r hs = mk_form (FhoareS hs) ty_bool

let f_hoareS hs_m hs_pr hs_s hs_po = 
  f_hoareS_r { hs_m; hs_pr; hs_s; hs_po; } 

let f_hoareF pre f post =
  let hf = { hf_pr = pre; hf_f = f; hf_po = post } in
    mk_form (FhoareF hf) ty_bool

(* -------------------------------------------------------------------- *)
let f_bdHoareS_r bhs = mk_form (FbdHoareS bhs) ty_bool

let f_bdHoareS mem pre s post hcmp bd = 
  f_bdHoareS_r { bhs_m = mem; bhs_pr = pre; bhs_s = s; bhs_po = post; 
                 bhs_cmp = hcmp; bhs_bd = bd } 

let f_bdHoareF bhf_pr bhf_f bhf_po bhf_cmp bhf_bd =
  let bhf = { bhf_pr; bhf_f; bhf_po; bhf_cmp; bhf_bd; } in
    mk_form (FbdHoareF bhf) ty_bool

let f_losslessF f = f_bdHoareF f_true f f_true FHeq f_r1

(* -------------------------------------------------------------------- *)
let f_equivS_r es = mk_form (FequivS es) ty_bool


let f_equivS es_ml es_mr es_pr es_sl es_sr es_po =
   f_equivS_r { es_ml; es_mr; es_pr; es_sl; es_sr; es_po; }

let f_equivF pre fl fr post = 
  let ef = { ef_pr = pre; ef_fl = fl; ef_fr = fr; ef_po = post } in
    mk_form (FequivF ef) ty_bool

(* -------------------------------------------------------------------- *)
let f_pr m f args e = mk_form (Fpr (m, f, args, e)) ty_real

(* -------------------------------------------------------------------- *)
let fop_int_le    = f_op EcCoreLib.p_int_le    [] (tfun tint  (tfun tint ty_bool))
let fop_int_lt    = f_op EcCoreLib.p_int_lt    [] (tfun tint  (tfun tint ty_bool))
let fop_int_prod = f_op EcCoreLib.p_int_prod [] (tfun tint  (tfun tint ty_int))
let fop_int_add  = f_op EcCoreLib.p_int_add  [] (tfun tint  (tfun tint ty_int))
let fop_int_sub  = f_op EcCoreLib.p_int_sub  [] (tfun tint  (tfun tint ty_int))
let fop_int_pow  = f_op EcCoreLib.p_int_pow  [] (tfun tint  (tfun tint ty_int))
let fop_real_le   = f_op EcCoreLib.p_real_le   [] (tfun treal (tfun treal ty_bool))
let fop_real_lt   = f_op EcCoreLib.p_real_lt   [] (tfun treal (tfun treal ty_bool))
let fop_real_add  = f_op EcCoreLib.p_real_add  [] (tfun treal (tfun treal treal))
let fop_real_sub  = f_op EcCoreLib.p_real_sub  [] (tfun treal (tfun treal treal))
let fop_real_prod = f_op EcCoreLib.p_real_prod [] (tfun treal (tfun treal treal))
let fop_real_div  = f_op EcCoreLib.p_real_div  [] (tfun treal (tfun treal treal))

let f_int_binop op f1 f2 =
  f_app op [f1;f2] ty_bool

let f_int_le = f_int_binop fop_int_le
let f_int_lt = f_int_binop fop_int_lt

let f_int_binop op f1 f2 =
  f_app op [f1; f2] ty_int

let f_int_prod = f_int_binop fop_int_prod
let f_int_add  = f_int_binop fop_int_add
let f_int_sub  = f_int_binop fop_int_sub
let f_int_pow  = f_int_binop fop_int_pow

let fop_int_intval = f_op EcCoreLib.p_int_intval [] (tfun tint (tfun tint (tfset tint)))

let f_int_intval k1 k2 = 
  f_app fop_int_intval [k1;k2] (tfset tint)

let fop_int_sum ty = f_op EcCoreLib.p_int_sum [ty] (tfun (tfun tint ty) (tfun (tfset tint) ty))

let f_int_sum op intval ty =
  f_app (fop_int_sum treal) [op;intval] ty

(* -------------------------------------------------------------------- *)
let f_real_cmp cmp f1 f2 =
  f_app cmp [f1; f2] ty_bool

let f_real_le = f_real_cmp fop_real_le
let f_real_lt = f_real_cmp fop_real_lt

let f_real_binop op f1 f2 =
  f_app op [f1; f2] ty_real

let f_real_add  = f_real_binop fop_real_add
let f_real_sub  = f_real_binop fop_real_sub
let f_real_prod = f_real_binop fop_real_prod
let f_real_div  = f_real_binop fop_real_div

(* -------------------------------------------------------------------- *)
let fop_in_supp ty = f_op EcCoreLib.p_in_supp [ty] (toarrow [ty; tdistr ty] tbool)
let fop_mu_x    ty = f_op EcCoreLib.p_mu_x    [ty] (toarrow [tdistr ty; ty] ty_real)
let fop_mu      ty = f_op EcCoreLib.p_mu      [ty] (tfun (tfun (tdistr ty) (tcpred ty)) ty_real)

let f_in_supp f1 f2 = f_app (fop_in_supp f1.f_ty) [f1; f2] ty_bool
let f_mu_x    f1 f2 = f_app (fop_mu_x f2.f_ty) [f1; f2] ty_real
let f_mu      f1 f2 = f_app (fop_mu (proj_distr_ty f1.f_ty)) [f1; f2] ty_real

let fop_weight ty = f_op EcCoreLib.p_weight [ty] (tfun (tdistr ty) treal)
let f_weight ty d = f_app (fop_weight ty) [d] treal

(* -------------------------------------------------------------------- *)
exception DestrError of string

let destr_error e = raise (DestrError e)

let is_op_and p = 
  EcPath.p_equal p EcCoreLib.p_and || EcPath.p_equal p EcCoreLib.p_anda

let is_op_or p = 
  EcPath.p_equal p EcCoreLib.p_or || EcPath.p_equal p EcCoreLib.p_ora

let destr_tuple f = 
  match f.f_node with
  | Ftuple fs -> fs
  | _ -> destr_error "tuple"

let destr_local f = 
  match f.f_node with
  | Flocal id -> id
  | _ -> destr_error "local"

let destr_and f = 
  match f.f_node with
  | Fapp({f_node = Fop(p,_)},[f1;f2]) when is_op_and p -> f1,f2
  | _ -> destr_error "and"

let destr_or f = 
  match f.f_node with
  | Fapp({f_node = Fop(p,_)},[f1;f2]) when is_op_or p -> f1,f2
  | _ -> destr_error "or" 

let destr_or_kind f = 
  match f.f_node with
  | Fapp({f_node = Fop(p,_)},[f1;f2]) when is_op_or p ->
    EcPath.p_equal p EcCoreLib.p_ora, f1,f2
  | _ -> destr_error "or" 

let destr_imp f = 
  match f.f_node with
  | Fapp({f_node = Fop(p,_)},[f1;f2]) when EcPath.p_equal p EcCoreLib.p_imp -> 
      f1,f2
  | _ -> destr_error "imp"

let destr_iff f = 
  match f.f_node with
  | Fapp({f_node = Fop(p,_)},[f1;f2]) when EcPath.p_equal p EcCoreLib.p_iff -> 
      f1,f2
  | _ -> destr_error "iff"

let destr_eq f = 
  match f.f_node with
  | Fapp({f_node = Fop(p,_)},[f1;f2]) when EcPath.p_equal p EcCoreLib.p_eq -> 
      f1,f2
  | _ -> destr_error "eq" 

let destr_eq_or_iff f = 
  match f.f_node with
  | Fapp({f_node = Fop(p,_)},[f1;f2]) when 
      EcPath.p_equal p EcCoreLib.p_iff || EcPath.p_equal p EcCoreLib.p_eq -> 
      f1,f2
  | _ -> destr_error "eq_or_iff"

let destr_not f = 
  match f.f_node with
  | Fapp({f_node = Fop(p,_)},[f1]) when EcPath.p_equal p EcCoreLib.p_not -> 
      f1
  | _ -> destr_error "not"

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
  | Fpr (m,f,a,ev) -> (m,f,a,ev)
  | _ -> destr_error "pr"

let destr_programS side f =
  match side, f.f_node with
  | None  , FhoareS   hs  -> (hs.hs_m, hs.hs_s)
  | None  , FbdHoareS bhs -> (bhs.bhs_m, bhs.bhs_s)
  | Some b, FequivS   es  -> begin
      match b with
      | true  -> (es.es_ml, es.es_sl)
      | false -> (es.es_mr, es.es_sr)
  end
  | _, _ -> destr_error "programS"

let destr_int f = 
  match f.f_node with
  | Fint n -> n
  | Fapp(op,[{f_node = Fint n}]) when f_equal op fop_int_opp -> -n
  | _ -> destr_error "destr_int" 

let destr_rint f = 
  match f.f_node with
  | Fapp (op,[f1]) when f_equal f_op_real_of_int op ->
    begin try destr_int f1 with DestrError _ -> destr_error "destr_rint" end
  | _ -> destr_error "destr_rint"


(* -------------------------------------------------------------------- *)
let is_from_destr dt f =
  try ignore (dt f); true with DestrError _ -> false

let is_true  f = f_equal f f_true
let is_false f = f_equal f f_false  

let is_tuple    f = is_from_destr destr_tuple     f
let is_local    f = is_from_destr destr_local     f
let is_and      f = is_from_destr destr_and       f
let is_or       f = is_from_destr destr_or        f
let is_not      f = is_from_destr destr_not       f
let is_imp      f = is_from_destr destr_imp       f
let is_iff      f = is_from_destr destr_iff       f
let is_eq       f = is_from_destr destr_eq        f
let is_forall   f = is_from_destr destr_forall1   f
let is_exists   f = is_from_destr destr_exists1   f
let is_let      f = is_from_destr destr_let1      f
let is_equivF   f = is_from_destr destr_equivF    f
let is_equivS   f = is_from_destr destr_equivS    f
let is_hoareS   f = is_from_destr destr_hoareS    f
let is_hoareF   f = is_from_destr destr_hoareF    f
let is_bdHoareS f = is_from_destr destr_bdHoareS  f
let is_bdHoareF f = is_from_destr destr_bdHoareF  f
let is_pr       f = is_from_destr destr_pr        f

let is_eq_or_iff f = (is_eq f) || (is_iff f)

(* -------------------------------------------------------------------- *)
module FSmart = struct
  type a_local = EcIdent.t * ty
  type a_pvar  = prog_var * ty * memory
  type a_quant = quantif * binding * form
  type a_if    = form tuple3
  type a_let   = lpattern * form * form
  type a_op    = EcPath.path * ty list * ty
  type a_tuple = form list
  type a_app   = form * form list * ty

  let f_local (fp, (x, ty)) (x', ty') =
    if   false && x == x' && ty == ty'
    then fp
    else f_local x' ty'

  let f_pvar (fp, (pv, ty, m)) (pv', ty', m') =
    if   false && pv == pv' && ty == ty' && m == m'
    then fp
    else f_pvar pv' ty' m'

  let f_quant (fp, (q, b, f)) (q', b', f') =
    if   false && q == q' && b == b' && f == f'
    then fp
    else f_quant q' b' f'

  let f_glob (fp, (mp, m)) (mp', m') =
    if   false && mp == mp' && m == m'
    then fp
    else f_glob mp' m'

  let f_if (fp, (c, f1, f2)) (c', f1', f2') =
    if   false && c == c' && f1 == f1' && f2 == f2'
    then fp
    else f_if c' f1' f2'

  let f_let (fp, (lp, f1, f2)) (lp', f1', f2') =
    if   false && lp == lp' && f1 == f1' && f2 == f2'
    then fp
    else f_let lp' f1' f2'

  let f_op (fp, (op, tys, ty)) (op', tys', ty') =
    if   false && op == op' && tys == tys' && ty == ty'
    then fp
    else f_op op' tys' ty'

  let f_app (fp, (f, fs, ty)) (f', fs', ty') =
    if   false && f == f' && fs == fs' && ty == ty'
    then fp
    else f_app f' fs' ty'

  let f_tuple (fp, fs) fs' =
    if false && fs == fs' then fp else f_tuple fs'

  let f_equivF (fp, ef) ef' =
    if eqf_equal ef ef' then fp else mk_form (FequivF ef') fp.f_ty

  let f_equivS (fp, es) es' =
    if eqs_equal es es' then fp else f_equivS_r es'

  let f_hoareF (fp, hf) hf' =
    if hf_equal hf hf' then fp else mk_form (FhoareF hf') fp.f_ty

  let f_hoareS (fp, hs) hs' =
    if hs_equal hs hs' then fp else f_hoareS_r hs'

  let f_bdHoareF (fp, bhf) bhf' =
    if bhf_equal bhf bhf' then fp else mk_form (FbdHoareF bhf') fp.f_ty

  let f_bdHoareS (fp, bhs) bhs' =
    if bhs_equal bhs bhs' then fp else f_bdHoareS_r bhs'

  let f_pr (fp, (m, mp, args, ev)) (m', mp', args', ev') =
    if   m == m' && mp == mp' && args == args' && ev == ev'
    then fp
    else f_pr m' mp' args' ev'
end

(* -------------------------------------------------------------------- *)
let f_map gt g fp =
  match fp.f_node with
  | Fquant(q, b, f) ->
      let map_gty ((x, gty) as b1) = 
        let gty' =
          match gty with
          | GTty ty ->
              let ty' = gt ty in
                if ty == ty' then gty else GTty ty'
          | _ -> gty
        in
          if gty == gty' then b1 else (x, gty')
      in

      let b' = List.smart_map map_gty b in
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
      let tys' = List.smart_map gt tys in
      let ty'  = gt fp.f_ty in
        FSmart.f_op (fp, (p, tys, fp.f_ty)) (p, tys', ty')

  | Fapp (f, fs) ->
      let f'  = g f in
      let fs' = List.smart_map g fs in
      let ty' = gt fp.f_ty in
        FSmart.f_app (fp, (f, fs, fp.f_ty)) (f', fs', ty')

  | Ftuple fs -> 
      let fs' = List.smart_map g fs in
        FSmart.f_tuple (fp, fs) fs'

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

  | Fpr (m, mp, args, ev) -> 
      let args' = List.smart_map g args in
      let ev'   = g ev in
        FSmart.f_pr (fp, (m, mp, args, ev)) (m, mp, args', ev')

(* -------------------------------------------------------------------- *)
let f_iter g f =
  match f.f_node with
  | Fquant(_,_,f1) -> g f1
  | Fif(f1,f2,f3) -> g f1;g f2; g f3
  | Flet(_,f1,f2) -> g f1;g f2
  | Fint _  | Flocal _ | Fpvar _ | Fglob _ | Fop _ -> ()
  | Fapp(e, es) -> g e; List.iter g es
  | Ftuple es -> List.iter g es
  | FhoareF hf -> g hf.hf_pr; g hf.hf_po
  | FhoareS hs -> g hs.hs_pr; g hs.hs_po
  | FbdHoareF bhf -> g bhf.bhf_pr; g bhf.bhf_po
  | FbdHoareS bhs -> g bhs.bhs_pr; g bhs.bhs_po
  | FequivF ef -> g ef.ef_pr; g ef.ef_po
  | FequivS es -> g es.es_pr; g es.es_po
  | Fpr(_,_,args,ev) -> List.iter g args; g ev

(* -------------------------------------------------------------------- *)
type f_subst = { 
  fs_freshen : bool; (* true means freshen locals *)
  fs_mp      : EcPath.mpath Mid.t;
  fs_loc     : form Mid.t;
  fs_mem     : EcIdent.t Mid.t;
  fs_sty     : ty_subst;
  fs_ty      : ty -> ty;
}

module Fsubst = struct
  (* ------------------------------------------------------------------ *)
  let f_subst_id = {
    fs_freshen = false;
    fs_mp      = Mid.empty;
    fs_loc     = Mid.empty;
    fs_mem     = Mid.empty;
    fs_sty     = ty_subst_id;
    fs_ty      = ty_subst ty_subst_id;
  }

  let is_subst_id s = 
       s.fs_freshen = false
    && is_ty_subst_id s.fs_sty
    && Mid.is_empty s.fs_loc
    && Mid.is_empty s.fs_mem

  let f_subst_init freshen smp sty =
    { f_subst_id
        with fs_freshen = freshen;
             fs_mp = smp;
             fs_sty = sty;
             fs_ty = ty_subst sty }

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
  let add_local s (x,t as xt) = 
    let x' = if s.fs_freshen then EcIdent.fresh x else x in
    let t' = s.fs_ty t in
      if   x == x' && t == t'
      then (s, xt)
      else f_bind_local s x (f_local x' t'), (x',t')

  let add_locals = List.smart_map_fold add_local

  let subst_lpattern (s: f_subst) (lp:lpattern) = 
    match lp with
    | LSymbol x ->
        let s, x' = add_local s x in
          if x == x' then (s, lp) else (s, LSymbol x')

    | LTuple xs ->
        let (s, xs') = add_locals s xs in
          if xs == xs' then (s, lp) else (s, LTuple xs')

  let gty_subst s gty = 
    if is_subst_id s then gty 
    else match gty with
    | GTty ty ->
      let ty' = s.fs_ty ty in
        if ty == ty' then gty else GTty ty'

    | GTmodty(p, (rx, r)) ->
      let sub = s.fs_sty.ts_mp in
      let p'  = mty_subst s.fs_sty.ts_p sub p in
      let xsub = EcPath.x_substm s.fs_sty.ts_p s.fs_mp in
      let rx' = 
        EcPath.Sx.fold
          (fun m rx' -> EcPath.Sx.add (xsub m) rx') rx
          EcPath.Sx.empty in
      let r'  = 
        EcPath.Sm.fold
          (fun m r' -> EcPath.Sm.add (sub m) r') r
          EcPath.Sm.empty
      in
        if p == p' && EcPath.Sx.equal rx rx' && EcPath.Sm.equal r r' then gty 
        else GTmodty(p', (rx', r'))

    | GTmem mt ->
      let mt' = EcMemory.mt_substm s.fs_sty.ts_p s.fs_mp s.fs_ty mt in
        if mt == mt' then gty else GTmem mt'
  
  (* ------------------------------------------------------------------ *)
  let add_binding s (x, gty as xt) =
    let gty' = gty_subst s gty in
    let x'   = if s.fs_freshen then EcIdent.fresh x else x in

    if x == x' && gty == gty' then (s, xt)
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

    | Fop (p, tys) ->
        let ty'  = s.fs_ty fp.f_ty in
        let tys' = List.smart_map s.fs_ty tys in
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
        let es  = e_subst_init s.fs_freshen s.fs_sty.ts_p s.fs_ty s.fs_mp in
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
      let es  = e_subst_init s.fs_freshen s.fs_sty.ts_p s.fs_ty s.fs_mp in
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
      let es = e_subst_init s.fs_freshen s.fs_sty.ts_p s.fs_ty s.fs_mp in
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

    | Fpr (m, mp, args, e) ->
      assert (not (Mid.mem mhr s.fs_mem));
      let m'    = Mid.find_def m m s.fs_mem in
      let mp'   = EcPath.x_substm s.fs_sty.ts_p s.fs_mp mp in
      let args' = List.smart_map (f_subst s) args in
      let e'    = (f_subst s) e in

      FSmart.f_pr (fp, (m, mp, args, e)) (m', mp', args', e')
  
    | _ -> f_map s.fs_ty (f_subst s) fp

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
    let sty = { ty_subst_id with ts_v = s } in
    { f_subst_id with fs_freshen = true; fs_sty = sty; fs_ty = ty_subst sty }

  let subst_tvar s = 
    let sf  = init_subst_tvar s in
    f_subst sf
end

let can_subst f = 
  match f.f_node with
  | Fint _ | Flocal _ | Fpvar _ | Fop _ -> true
  | _ -> false

(* -------------------------------------------------------------------- *)
let rec gcd a b = if b = 0 then a else gcd b (a mod b)

let f_int_opp_simpl f = 
  match f.f_node with
  | Fapp(op,[f]) when f_equal op fop_int_opp -> f
  | _ -> 
    if f_equal f_i0 f then f_i0 else f_int_opp f 

let f_int_add_simpl f1 f2 =
  try f_int (destr_int f1 + destr_int f2)
  with DestrError _ -> 
    if f_equal f_i0 f1 then f2
    else if f_equal f_i0 f2 then f1
    else f_int_add f1 f2

let f_int_sub_simpl f1 f2 =
  if f_equal f1 f2 then f_i0
  else
    try f_int (destr_int f1 - destr_int f2)
    with DestrError _ -> 
      if f_equal f_i0 f1 then f_int_opp_simpl f2
      else if f_equal f_i0 f2 then f1
      else f_int_sub f1 f2

let f_int_prod_simpl f1 f2 =
  try f_int (destr_int f1 * destr_int f2)
  with DestrError _ -> 
    if f_equal f_i0 f1 || f_equal f_i0 f2 then f_i0
    else if f_equal f_i1 f1 then f2
    else if f_equal f_i1 f2 then f1
    else f_int_prod f1 f2

let destr_rdivint f =
  match f.f_node with
  | Fapp(op,[f1;f2]) when f_equal op fop_real_div ->
    begin 
      try destr_rint f1, destr_rint f2 
      with DestrError _ -> destr_error "rdivint" 
    end
  | _ -> destr_error "rdivint" 

let norm_real_int_div n1 n2 =
  if n2 = 0 then f_real_div (f_rint n1) (f_rint n2)
  else
    let n = gcd n1 n2 in
    let n1, n2 = if n <> 1 then n1/n, n2/n else n1, n2 in
    if n1 = 0 then f_r0 
    else if n2 = 1 then f_rint n1
    else if n2 < 0 then f_real_div (f_rint (-n1)) (f_rint (-n2))
    else f_real_div (f_rint n1) (f_rint n2)

let f_real_add_simpl f1 f2 =
  try f_rint (destr_rint f1 + destr_rint f2)
  with DestrError _ -> 
    try 
      let (n1,d1), (n2,d2) = destr_rdivint f1, destr_rdivint f2 in
      if d1 = 0 || d2 = 0 then destr_error "";
      norm_real_int_div (n1*d2 + n2*d1) (d1*d2)
    with DestrError _ ->
      if f_equal f_r0 f1 then f2
      else if f_equal f_r0 f2 then f1
      else f_real_add f1 f2

let f_real_sub_simpl f1 f2 =
  try f_rint (destr_rint f1 - destr_rint f2)
  with DestrError _ -> 
    try 
      let (n1,d1), (n2,d2) = destr_rdivint f1, destr_rdivint f2 in
      if d1 = 0 || d2 = 0 then destr_error "";
      norm_real_int_div (n1*d2 - n2*d1) (d1*d2)
    with DestrError _ ->
      if f_equal f_r0 f2 then f1
      else f_real_sub f1 f2

let rec f_real_prod_simpl f1 f2 =
  match f1.f_node, f2.f_node with
  | Fapp (op1,[f1_1;f1_2]), Fapp (op2,[f2_1;f2_2]) 
    when f_equal op1 fop_real_div && f_equal op2 fop_real_div ->
    f_real_div_simpl (f_real_prod_simpl f1_1 f2_1) (f_real_prod_simpl f1_2 f2_2)
  | _, Fapp (op2,[f2_1;f2_2]) when f_equal op2 fop_real_div ->
    f_real_div_simpl (f_real_prod_simpl f1 f2_1) f2_2
  | Fapp (op1,[f1_1;f1_2]), _ when f_equal op1 fop_real_div ->
    f_real_div_simpl (f_real_prod_simpl f1_1 f2) f1_2
  | _ ->
    try f_rint (destr_rint f1 * destr_rint f2)
    with DestrError _ ->   
      if f_equal f_r0 f1 || f_equal f_r0 f2 then f_r0
      else if f_equal f_r1 f1 then f2
      else if f_equal f_r1 f2 then f1
      else f_real_prod f1 f2

and f_real_div_simpl f1 f2 =
  match f1.f_node, f2.f_node with
  | Fapp (op1,[f1_1;f1_2]), Fapp (op2,[f2_1;f2_2]) 
    when f_equal op1 fop_real_div && f_equal op2 fop_real_div ->
    f_real_div_simpl (f_real_prod_simpl f1_1 f2_2) (f_real_prod_simpl f1_2 f2_1)
  | _, Fapp (op2,[f2_1;f2_2]) 
    when f_equal op2 fop_real_div ->
    f_real_div_simpl (f_real_prod_simpl f1 f2_2) f2_1
  | Fapp (op,[f1_1;f1_2]), _ 
    when f_equal op fop_real_div ->
    f_real_div_simpl f1_1 (f_real_prod_simpl f1_2 f2)
  | _ -> 
    try norm_real_int_div (destr_rint f1) (destr_rint f2)
    with DestrError _ ->
      if f_equal f2 f_r1 then f1 
      else f_real_div f1 f2


(* -------------------------------------------------------------------- *)
let f_let_simpl lp f1 f2 =
  match lp, f1.f_node with
  | LSymbol (id,_), _ ->
      let n = Mid.find_def 0 id (f_fv f2) in
      if n = 0 then f2 
      else if n = 1 || can_subst f1 then Fsubst.subst_local id f1 f2
      else f_let lp f1 f2 
  | LTuple ids, Ftuple fs ->
      let d, s = 
        List.fold_left2 (fun (d,s) (id,ty) f1 ->
          let n = Mid.find_def 0 id (f_fv f2) in
          if n = 0 then (d,s) 
          else if n = 1 || can_subst f1 then (d,Mid.add id f1 s)
          else (((id,ty),f1)::d,s)) ([],Mid.empty) ids fs in
      List.fold_left (fun f2 (id,f1) -> f_let (LSymbol id) f1 f2)
        (Fsubst.subst_locals s f2) d
  | LTuple ids, _ ->
    if List.for_all (fun (id,_) -> Mid.find_def 0 id (f_fv f2) = 0) ids then f2
    else f_let lp f1 f2 

let f_lets_simpl =
  (* FIXME : optimize this *)
  List.fold_right (fun (lp,f1) f2 -> f_let_simpl lp f1 f2) 

let rec f_app_simpl f args ty = 
  if args = [] then f 
  else match f.f_node,args with
    | Fquant (Llambda, bds,f), args -> 
      f_betared_simpl Fsubst.f_subst_id bds f args ty
    | Fapp(f',args'),_ -> mk_form (Fapp(f', args'@args)) ty
    | _ -> mk_form (Fapp(f,args)) ty 

and f_betared_simpl subst bds f args ty =
  match bds, args with
  | (x,GTty _)::bds, arg :: args ->
    f_betared_simpl (Fsubst.f_bind_local subst x arg) bds f args ty
  | (_,_)::_, _ :: _ -> assert false
  | _, [] -> f_lambda bds (Fsubst.f_subst subst f) 
  | [], _ -> f_app_simpl (Fsubst.f_subst subst f) args ty

let f_betared_simpl bds f args ty = 
  f_betared_simpl Fsubst.f_subst_id bds f args ty

let f_forall_simpl b f = 
  let b = List.filter (fun (id,_) -> Mid.mem id (f_fv f)) b in
  f_forall b f 

let f_exists_simpl b f = 
  let b = List.filter (fun (id,_) -> Mid.mem id (f_fv f)) b in
  f_exists b f 

let f_quant_simpl q b f =
  if q = Lforall then f_forall_simpl b f else f_exists b f

let f_not_simpl f = 
  if is_not f then destr_not f
  else if is_true f then f_false
  else if is_false f then f_true
  else f_not f

let f_and_simpl f1 f2 = 
  if is_true f1 then f2
  else if is_false f1 then f_false
  else if is_true f2 then f1
  else if is_false f2 then f_false 
  else f_and f1 f2

let f_ands_simpl = List.fold_right f_and_simpl

let f_anda_simpl f1 f2 = 
  if is_true f1 then f2
  else if is_false f1 then f_false
  else if is_true f2 then f1
  else if is_false f2 then f_false 
  else f_anda f1 f2

let f_or_simpl f1 f2 = 
  if is_true f1 then f_true
  else if is_false f1 then f2 
  else if is_true f2 then f_true
  else if is_false f2 then f1
  else f_or f1 f2

let f_ora_simpl f1 f2 = 
  if is_true f1 then f_true
  else if is_false f1 then f2 
  else if is_true f2 then f_true
  else if is_false f2 then f1
  else f_ora f1 f2

let f_imp_simpl f1 f2 = 
  if is_true f1 then f2
  else if is_false f1 || is_true f2 then f_true
  else if is_false f2 then f_not_simpl f1
  else 
    if f_equal f1 f2 then f_true
    else f_imp f1 f2 
    (* FIXME : simplify x = f1 => f2 into x = f1 => f2{x<-f2} *)

let bool_val f = 
  if is_true f then Some true
  else if is_false f then Some false
  else None 

let f_if_simpl f1 f2 f3 =
  if f_equal f2 f3 then f2
  else match bool_val f1, bool_val f2, bool_val f3 with
  | Some true, _, _  -> f2
  | Some false, _, _ -> f3
  | _, Some true, _  -> f_imp_simpl (f_not_simpl f1) f3
  | _, Some false, _ -> f_anda_simpl (f_not_simpl f1) f3
  | _, _, Some true  -> f_imp_simpl f1 f2
  | _, _, Some false -> f_anda_simpl f1 f2
  | _, _, _          -> f_if f1 f2 f3

let f_imps_simpl = List.fold_right f_imp_simpl 
let f_imps = List.fold_right f_imp 

let f_iff_simpl f1 f2 = 
  if f_equal f1 f2 then f_true
  else if is_true f1 then f2
  else if is_false f1 then f_not_simpl f2
  else if is_true f2 then f1
  else if is_false f2 then f_not_simpl f1
  else f_iff f1 f2

let f_eq_simpl f1 f2 = 
  if f_equal f1 f2 then f_true
  else match f1.f_node, f2.f_node with
  | Fint _ , Fint _ -> f_false
  | Fapp(op1, [{f_node = Fint _}]), Fapp(op2,[{f_node = Fint _}]) 
    when f_equal op1 f_op_real_of_int && 
      f_equal op2 f_op_real_of_int ->
    f_false 
  | Fop(op1, []) ,Fop (op2, []) when
    (EcPath.p_equal op1 EcCoreLib.p_true &&
     EcPath.p_equal op2 EcCoreLib.p_false) ||
     (EcPath.p_equal op2 EcCoreLib.p_true &&
     EcPath.p_equal op1 EcCoreLib.p_false) -> f_false
  | _ -> f_eq f1 f2

let f_int_le_simpl f1 f2 = 
  if f_equal f1 f2 then f_true
  else match f1.f_node, f2.f_node with
  | Fint x1 , Fint x2 -> f_bool (x1 <= x2)
  | _, _ -> f_int_le f1 f2 

let f_int_lt_simpl f1 f2 = 
  if f_equal f1 f2 then f_false
  else match f1.f_node, f2.f_node with
  | Fint x1 , Fint x2 -> f_bool (x1 < x2)
  | _, _ -> f_int_lt f1 f2 

let f_real_le_simpl f1 f2 =
  if f_equal f1 f2 then f_true
  else match f1.f_node, f2.f_node with
  | Fapp(op1, [{f_node = Fint x1}]), Fapp(op2, [{f_node = Fint x2}]) 
    when f_equal op1 f_op_real_of_int && f_equal op2 f_op_real_of_int -> 
    f_bool (x1 <= x2)
  | _, _ -> f_real_le f1 f2 

let f_real_lt_simpl f1 f2 =
  if f_equal f1 f2 then f_false
  else match f1.f_node, f2.f_node with
  | Fapp(op1, [{f_node = Fint x1}]), Fapp(op2, [{f_node = Fint x2}]) 
    when f_equal op1 f_op_real_of_int && f_equal op2 f_op_real_of_int -> 
    f_bool (x1 < x2)
  | _, _ -> f_real_lt f1 f2  

  


(* -------------------------------------------------------------------- *)
let rec form_of_expr mem (e: expr) = 
  match e.e_node with
  | Eint n -> f_int n
  | Elocal id -> f_local id e.e_ty
  | Evar pv -> f_pvar pv e.e_ty mem
  | Eop (op,tys) -> f_op op tys e.e_ty
  | Eapp (ef,es) -> 
      f_app (form_of_expr mem ef) (List.map (form_of_expr mem) es) e.e_ty
  | Elet (lpt,e1,e2) -> f_let lpt (form_of_expr mem e1) (form_of_expr mem e2)
  | Etuple es -> f_tuple (List.map (form_of_expr mem) es)
  | Eif (e1,e2,e3) -> 
      f_if (form_of_expr mem e1) (form_of_expr mem e2) (form_of_expr mem e3)
  | Elam(b,e) ->
    f_lambda (List.map (fun (x,ty) -> (x,GTty ty)) b) (form_of_expr mem e)

(* -------------------------------------------------------------------- *)
type op_kind = 
  | OK_true
  | OK_false
  | OK_not
  | OK_and   of bool
  | OK_or    of bool
  | OK_imp
  | OK_iff
  | OK_eq
  | OK_int_le
  | OK_int_lt
  | OK_real_le
  | OK_real_lt
  | OK_int_add
  | OK_int_sub
  | OK_int_prod
  | OK_real_add
  | OK_real_sub
  | OK_real_prod
  | OK_real_div
  | OK_other 

let operators =
  let operators =
    [EcCoreLib.p_true , OK_true;
     EcCoreLib.p_false, OK_false;
     EcCoreLib.p_not  , OK_not; 
     EcCoreLib.p_anda , OK_and true;
     EcCoreLib.p_and  , OK_and false; 
     EcCoreLib.p_ora  , OK_or true;
     EcCoreLib.p_or   , OK_or  false;
     EcCoreLib.p_imp  , OK_imp;
     EcCoreLib.p_iff  , OK_iff;
     EcCoreLib.p_eq   , OK_eq;
     EcCoreLib.p_int_le, OK_int_le;
     EcCoreLib.p_int_lt, OK_int_lt;
     EcCoreLib.p_real_le, OK_real_le;
     EcCoreLib.p_real_lt, OK_real_lt;
     EcCoreLib.p_int_add, OK_int_add;
     EcCoreLib.p_int_sub, OK_int_sub;
     EcCoreLib.p_int_prod, OK_int_prod;
     EcCoreLib.p_real_add, OK_real_add;
     EcCoreLib.p_real_sub, OK_real_sub;
     EcCoreLib.p_real_prod, OK_real_prod;
     EcCoreLib.p_real_div, OK_real_div
    ]
  in

  let tbl = EcPath.Hp.create 11 in
    List.iter (fun (p, k) -> EcPath.Hp.add tbl p k) operators;
    tbl

let op_kind (p : EcPath.path) = 
  try EcPath.Hp.find operators p with Not_found -> OK_other

let is_logical_op op =
  match op_kind op with
  | OK_not | OK_and _ | OK_or _ | OK_imp | OK_iff | OK_eq 
  | OK_int_le| OK_int_lt | OK_real_le | OK_real_lt 
  | OK_int_add | OK_int_sub | OK_int_prod 
  | OK_real_add | OK_real_sub| OK_real_prod | OK_real_div -> true
  | _ -> false

(* -------------------------------------------------------------------- *)
type sform =
  | SFint   of int
  | SFlocal of EcIdent.t
  | SFpvar  of EcTypes.prog_var * memory
  | SFglob  of EcPath.mpath * memory 

  | SFif    of form * form * form
  | SFlet   of lpattern * form * form
  | SFtuple of form list

  | SFquant of quantif * (EcIdent.t * gty) * form
  | SFtrue
  | SFfalse
  | SFnot   of form
  | SFand   of bool * (form * form)
  | SFor    of bool * (form * form)
  | SFimp   of form * form
  | SFiff   of form * form
  | SFeq    of form * form
  | SFop    of (EcPath.path * ty list) * (form list)

  | SFhoareF   of hoareF
  | SFhoareS   of hoareS
  | SFbdHoareF of bdHoareF
  | SFbdHoareS of bdHoareS
  | SFequivF   of equivF
  | SFequivS   of equivS
  | SFpr       of pr

  | SFother of form

let sform_of_op (op, ty) args =
  match op_kind op, args with
  | OK_true , [] -> SFtrue
  | OK_false, [] -> SFfalse
  | OK_not  , [f] -> SFnot f
  | OK_and b, [f1; f2] -> SFand (b, (f1, f2))
  | OK_or  b, [f1; f2] -> SFor  (b, (f1, f2))
  | OK_imp  , [f1; f2] -> SFimp (f1, f2)
  | OK_iff  , [f1; f2] -> SFiff (f1, f2)
  | OK_eq   , [f1; f2] -> SFeq  (f1, f2)
  | _ -> SFop ((op, ty), args)

let rec sform_of_form fp =
  match fp.f_node with
  | Fint   i      -> SFint   i
  | Flocal x      -> SFlocal x
  | Fpvar (x, me) -> SFpvar  (x, me)
  | Fglob (m, me) -> SFglob  (m, me)

  | Fif    (c, f1, f2)  -> SFif    (c, f1, f2)
  | Flet   (lv, f1, f2) -> SFlet   (lv, f1, f2)
  | Ftuple fs           -> SFtuple fs

  | Fquant (_, [ ]  , f) -> sform_of_form f
  | Fquant (q, [b]  , f) -> SFquant (q, b, f)
  | Fquant (q, b::bs, f) -> SFquant (q, b, f_quant q bs f)

  | FhoareF   hf -> SFhoareF   hf
  | FhoareS   hs -> SFhoareS   hs
  | FbdHoareF hf -> SFbdHoareF hf
  | FbdHoareS hs -> SFbdHoareS hs
  | FequivF   ef -> SFequivF   ef
  | FequivS   es -> SFequivS   es
  | Fpr       pr -> SFpr       pr

  | Fop (op, ty) ->
      sform_of_op (op, ty) []

  | Fapp ({ f_node = Fop (op, ty) }, args) ->
      sform_of_op (op, ty) args

  | _ -> SFother fp

(* -------------------------------------------------------------------- *)
let f_check_uni f =  
  let rec aux f =
    ty_check_uni f.f_ty;
    match f.f_node with
    | Fquant(_,b,f) ->
      let check_gty = function
        | (_,GTty ty) -> ty_check_uni ty
        | _ -> () in
      List.iter check_gty b;
      aux f
    | Fop(_,tys) -> List.iter ty_check_uni tys
    | _ -> f_iter aux f in
  try aux f;true with EcTypes.FoundUnivar -> false

(* -------------------------------------------------------------------- *)
let rec lp_dump (lp : lpattern) =
  match lp with
  | LSymbol (x,_) ->
      dleaf "LSymbol (%s)" (EcIdent.tostring x)

  | LTuple xs ->
      let xs = List.map (fun (x,_) -> EcIdent.tostring x) xs in
        dleaf "LTuple (%s)" (String.concat ", " xs)

let string_of_quantif = function
  | Lforall -> "Lforall"
  | Lexists -> "Lexists"
  | Llambda -> "Llambda"

let gty_dump (gty : gty) =
  match gty with
  | GTty    t -> dnode "GTty" [ty_dump t]
  | GTmodty _ -> dleaf "GTmodty"
  | GTmem   _ -> dleaf "GTmem"

let bd_dump (x, gty) =
  dnode
    (Printf.sprintf "binding (%s)" (EcIdent.tostring x))
    [gty_dump gty]

let rec f_dump (f : form) : dnode =
  let node =
    match f.f_node with
    | Fquant (q, b, f) ->
        dnode
          (Printf.sprintf "Fquant (%s)" (string_of_quantif q))
          (List.flatten [List.map bd_dump b; [f_dump f]])
  
    | Flocal x ->
        dleaf "Flocal (%s)" (EcIdent.tostring x)
  
    | Fint i ->
        dleaf "Fint (%d)"  i
  
    | Fpvar (x, m) ->
        dleaf "Fpvar (%s, %s)" (string_of_pvar x) (EcIdent.tostring m)
  
    | Fif (c, f1, f2) ->
        dnode "Fif" (List.map f_dump [c; f1; f2])
  
    | Flet (p, f1, f2) ->
        dnode "Flet" [lp_dump p; f_dump f1; f_dump f2]
  
    | Fapp (f, fs) ->
        dnode "Fapp" [f_dump f; dnode "arguments" (List.map f_dump fs)]
  
    | Fop (p, tys) ->
        dnode
          (Printf.sprintf "Fop (%s)" (EcPath.tostring p))
          [dnode "type-arguments" (List.map ty_dump tys)]
  
    | Ftuple fs ->
        dnode "Ftuple" (List.map f_dump fs)
  
    | Fglob _ -> dleaf "Fglob"
    | FhoareF _ -> dleaf "FhoareF"
    | FhoareS _ -> dleaf "FhoareS"
    | FbdHoareF _ -> dleaf "FbdHoareF"
    | FbdHoareS _ -> dleaf "FbdHoareS"
    | FequivF _ -> dleaf "FequivF"
    | FequivS _ -> dleaf "FequivS"
    | Fpr     _ -> dleaf "Fpr"
  in
     dnode "Form" [ty_dump f.f_ty; node]
