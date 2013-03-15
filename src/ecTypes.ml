(* -------------------------------------------------------------------- *)
open EcDebug
open EcUtils
open EcSymbols
open EcIdent
open EcPath
open EcUidgen

(* -------------------------------------------------------------------- *)
type ty = {
  ty_node : ty_node;
  ty_tag  : int;
}

and ty_node =
  | Tunivar of EcUidgen.uid
  | Tvar    of EcIdent.t 
  | Ttuple  of ty list
  | Tconstr of EcPath.path * ty list
  | Tfun    of ty * ty

type dom = ty list
type tysig = dom * ty 

let ty_equal : ty -> ty -> bool = (==)
let ty_hash ty = ty.ty_tag

module Hsty = Why3.Hashcons.Make (struct
  type t = ty

  let equal ty1 ty2 =
    match ty1.ty_node, ty2.ty_node with
    | Tunivar u1      , Tunivar u2       -> 
        uid_equal u1 u2
    | Tvar v1         , Tvar v2          -> 
        id_equal v1 v2
    | Ttuple lt1      , Ttuple lt2       -> 
        List.all2 ty_equal lt1 lt2
    | Tconstr (p1,lt1), Tconstr (p2,lt2) -> 
        EcPath.p_equal p1 p2 && List.all2 ty_equal lt1 lt2
    | Tfun(d1,c1)     , Tfun(d2,c2)      -> 
        ty_equal d1 d2 && ty_equal c1 c2
    | _               , _                -> false
      
  let hash ty = 
    match ty.ty_node with 
    | Tunivar u      -> 
        u
    | Tvar    id     -> 
        EcIdent.tag id
    | Ttuple  tl     -> 
        Why3.Hashcons.combine_list ty_hash 0 tl
    | Tconstr (p,tl) -> 
        Why3.Hashcons.combine_list ty_hash p.p_tag tl
    | Tfun    (t1,t2) ->
        Why3.Hashcons.combine (ty_hash t1) (ty_hash t2)
          
  let tag n ty = { ty with ty_tag = n }
      
end)

let mk_ty node =  Hsty.hashcons { ty_node = node; ty_tag = -1 }

module MSHty = EcMaps.MakeMSH(struct 
  type t = ty
  let tag t = t.ty_tag 
end)

module Mty = MSHty.M
module Sty = MSHty.S
module Hty = MSHty.H

(* -------------------------------------------------------------------- *)
let tuni uid = mk_ty (Tunivar uid)

let tvar id = mk_ty (Tvar id)

let ttuple lt    = mk_ty (Ttuple lt)
let tconstr p lt = mk_ty (Tconstr(p,lt))
let tfun t1 t2   = mk_ty (Tfun(t1,t2)) 

(* -------------------------------------------------------------------- *)
let tunit      = tconstr EcCoreLib.p_unit  []
let tbool      = tconstr EcCoreLib.p_bool  []
let tint       = tconstr EcCoreLib.p_int   []
let tdistr  ty = tconstr EcCoreLib.p_distr [ty]
let treal      = tconstr EcCoreLib.p_real  []
 
let toarrow dom ty = 
  List.fold_right tfun dom ty

(* -------------------------------------------------------------------- *)
let rec ty_dump (ty : ty) =
  match ty.ty_node with
  | Tunivar i ->
      dleaf "Tunivar (%d)" i

  | Tvar x ->
      dleaf "Tvar (%s)" (EcIdent.tostring x)

  | Ttuple ts ->
      dnode "Ttuple" (List.map ty_dump ts)

  | Tconstr (p, ts) ->
      dnode
        (Printf.sprintf "Tconstr (%s)" (EcPath.tostring p))
        (List.map ty_dump ts)

  | Tfun (ty1, ty2) ->
      dnode "Tfun" [ty_dump ty1; ty_dump ty2]

(* -------------------------------------------------------------------- *)
let dom_dump (dom : dom) =
  dnode "domain" (List.map ty_dump dom)

(* -------------------------------------------------------------------- *)
let ty_map f t = 
  match t.ty_node with 
  | Tunivar _ | Tvar _ -> t
  | Ttuple lty -> 
      let lty' = List.smart_map f lty in
      if lty == lty' then t else
      ttuple lty'
  | Tconstr(p, lty) -> 
      let lty' = List.smart_map f lty in
      if lty == lty' then t else
      tconstr p lty'
  | Tfun(t1,t2) -> 
      let t1' = f t1 and t2' = f t2 in
      if t1 == t1' && t2 == t2' then t else
      tfun t1' t2'

let ty_fold f s ty = 
  match ty.ty_node with 
  | Tunivar _ | Tvar _ -> s
  | Ttuple lty -> List.fold_left f s lty
  | Tconstr(_, lty) -> List.fold_left f s lty
  | Tfun(t1,t2) -> f (f s t1) t2

let ty_sub_exists f t =
  match t.ty_node with
  | Tunivar _ | Tvar _ -> false
  | Ttuple lty -> List.exists f lty
  | Tconstr (_, lty) -> List.exists f lty
  | Tfun (t1,t2) -> f t1 || f t2
  
(* -------------------------------------------------------------------- *)
type ty_subst = {
    ts_p : EcPath.path -> EcPath.path;
    ts_u : ty Muid.t;
    ts_v : ty Mid.t;
  }

let ty_subst_id = 
  { ts_p = identity;
    ts_u = Muid.empty;
    ts_v = Mid.empty }

let ty_subst s =
  Hty.memo_rec 107 (fun aux ty ->
    match ty.ty_node with 
    | Tunivar id -> 
        odfl ty (Muid.find_opt id s.ts_u) 
    | Tvar id    -> odfl ty (Mid.find_opt  id s.ts_v)
    | Ttuple lty -> 
      let lty' = List.smart_map aux lty in
      if lty == lty' then ty else
      ttuple lty'
    | Tconstr(p, lty) -> 
        let lty' = List.smart_map aux lty in
        let p' = s.ts_p p in
        if p == p' && lty == lty' then ty else
        tconstr p' lty'
    | Tfun(t1,t2) -> 
        let t1' = aux t1 and t2' = aux t2 in
        if t1 == t1' && t2 == t2' then ty else
        tfun t1' t2')

module Tuni = struct
  let subst1 ((id, t) : uid * ty) =
    ty_subst { ty_subst_id with ts_u = Muid.singleton id t }
        
  let subst (uidmap : ty Muid.t) =
    ty_subst { ty_subst_id with ts_u = uidmap } 

  let subst_dom uidmap = List.map (subst uidmap)

  let occur u = 
    let rec aux t = 
      match t.ty_node with
      | Tunivar u' -> uid_equal u u'
      | _ -> ty_sub_exists aux t in
    aux

  let rec fv_rec fv t = 
    match t.ty_node with
    | Tunivar id -> Suid.add id fv 
    | _ -> ty_fold fv_rec fv t 

  let fv = fv_rec Suid.empty

  let fv_sig (dom, codom) = 
    List.fold_left fv_rec (fv codom) dom
end

module Tvar = struct 
  let subst1 (id,t) = 
    ty_subst { ty_subst_id with ts_v = Mid.singleton id t }

  let subst (s : ty Mid.t) =
    ty_subst { ty_subst_id with ts_v = s }

  let init lv lt = 
    assert (List.length lv = List.length lt);
    List.fold_left2 (fun s v t -> Mid.add v t s) Mid.empty lv lt

  let rec fv_rec fv t = 
    match t.ty_node with
    | Tvar id -> Sid.add id fv 
    | _ -> ty_fold fv_rec fv t 

  let fv = fv_rec Sid.empty

  let fv_sig (dom, codom) = 
    List.fold_left fv_rec (fv codom) dom

end

(* -------------------------------------------------------------------- *)
type pvar_kind = 
  | PVglob
  | PVloc 

type prog_var = {
  pv_name : EcPath.mpath;
  pv_kind : pvar_kind;
}

let pv_equal v1 v2 = 
  EcPath.m_equal v1.pv_name v2.pv_name && v1.pv_kind = v2.pv_kind 

let pv_hash v = 
  Why3.Hashcons.combine (EcPath.m_hash v.pv_name)
    (if v.pv_kind = PVglob then 1 else 0)

let pv_compare v1 v2 = 
  let r = EcPath.m_compare v1.pv_name v2.pv_name in
  if r = 0 then Pervasives.compare v1.pv_kind v2.pv_kind
  else r 

let is_loc v = match v.pv_kind with PVloc -> true | _ -> false
  
let pv_subst m_subst pv = 
  let mp' = m_subst pv.pv_name in
  if pv.pv_name == mp' then pv else { pv with pv_name = mp'}

let string_of_pvar_kind = function
  | PVglob -> "PVglob"
  | PVloc  -> "PVloc"

let string_of_pvar (p : prog_var) =
  Printf.sprintf "%s[%s]"
    (EcPath.m_tostring p.pv_name)
    (string_of_pvar_kind p.pv_kind)

(* -------------------------------------------------------------------- *)
type lpattern =
  | LSymbol of (EcIdent.t * ty)
  | LTuple  of (EcIdent.t * ty) list

let idty_equal (x1,t1) (x2,t2) = 
  EcIdent.id_equal x1 x2 && ty_equal t1 t2

let lp_equal p1 p2 = 
  match p1, p2 with
  | LSymbol xt1, LSymbol xt2 -> idty_equal xt1 xt2 
  | LTuple lx1, LTuple lx2 -> List.all2 idty_equal lx1 lx2
  | _ -> false

let idty_hash (x,t) = Why3.Hashcons.combine (EcIdent.id_hash x) (ty_hash t) 

let lp_hash = function
  | LSymbol x -> idty_hash x
  | LTuple lx -> Why3.Hashcons.combine_list idty_hash 0 lx

(* -------------------------------------------------------------------- *)
type expr = {
  e_node : expr_node;
  e_ty   : ty;
  e_fv   : int Mid.t; 
  e_tag  : int;
}

and expr_node =
  | Eint   of int                        (* int. literal          *)
  | Elocal of EcIdent.t                  (* let-variables         *)
  | Evar   of prog_var                   (* module variable       *)
  | Eop    of EcPath.path * ty list      (* op apply to type args *)
  | Eapp   of expr * expr list       (* op. application       *)
  | Elet   of lpattern * expr * expr (* let binding           *)
  | Etuple of expr list                (* tuple constructor     *)
  | Eif    of expr * expr * expr   (* _ ? _ : _             *)



(* -------------------------------------------------------------------- *)
let e_equal   = ((==) : expr -> expr -> bool)
let e_hash    = fun e -> e.e_tag
let e_compare = fun e1 e2 -> e_hash e1 - e_hash e2
let e_fv e    = e.e_fv 
let e_ty e = e.e_ty

(* -------------------------------------------------------------------- *)

let lp_fv = function
  | LSymbol (id,_) -> Sid.singleton id
  | LTuple ids -> 
      List.fold_left (fun s (id,_) -> Sid.add id s) Sid.empty ids

let pv_fv pv = EcPath.m_fv Mid.empty pv.pv_name

let fv_node = function 
  | Eint _ | Eop _ -> Mid.empty
  | Evar v   -> pv_fv v 
  | Elocal id -> fv_singleton id 
  | Eapp(f,args) ->
    List.fold_left (fun s e -> fv_union s (e_fv e)) (e_fv f) args
  | Elet(lp,e1,e2) ->
    fv_union (e_fv e1) (fv_diff (e_fv e2) (lp_fv lp))
  | Etuple es ->
    List.fold_left (fun s e -> fv_union s (e_fv e)) Mid.empty es
  | Eif(e1,e2,e3) ->
      fv_union (e_fv e1) (fv_union (e_fv e2) (e_fv e3))

(* -------------------------------------------------------------------- *)
module Hexpr = Why3.Hashcons.Make (struct 
  type t = expr

  let equal_node e1 e2 =
    match e1, e2 with
    | Eint   i1, Eint   i2 -> i1 == i2
    | Elocal x1, Elocal x2 -> EcIdent.id_equal x1 x2 
    | Evar   x1, Evar   x2 -> pv_equal x1 x2

    | Eop (p1, tys1), Eop (p2, tys2) ->
           (EcPath.p_equal p1 p2)
        && (List.all2 ty_equal tys1 tys2)

    | Eapp (e1, es1), Eapp (e2, es2) ->
           (e_equal e1 e2)
        && (List.all2 e_equal es1 es2)

    | Elet (lp1, e1, f1), Elet (lp2, e2, f2) ->
        (lp_equal lp1 lp2) && (e_equal e1 e2) && (e_equal f1 f2)

    | Etuple es1, Etuple es2 ->
        List.all2 e_equal es1 es2

    | Eif (c1, e1, f1), Eif (c2, e2, f2) ->
        (e_equal c1 c2) && (e_equal e1 e2) && (e_equal f1 f2)

    | _, _ -> false

  let equal e1 e2 = 
    equal_node e1.e_node e2.e_node && 
    ty_equal e1.e_ty e2.e_ty 

  let hash e = 
    match e.e_node with
    | Eint   i -> Hashtbl.hash i
    | Elocal x -> Hashtbl.hash x
    | Evar   x -> pv_hash x

    | Eop (p, tys) ->
        Why3.Hashcons.combine_list ty_hash
          (EcPath.p_hash p) tys

    | Eapp (e, es) ->
        Why3.Hashcons.combine_list e_hash (e_hash e) es

    | Elet (p, e1, e2) ->
        Why3.Hashcons.combine2
          (lp_hash p) (e_hash e1) (e_hash e2)

    | Etuple es ->
        Why3.Hashcons.combine_list e_hash 0 es

    | Eif (c, e1, e2) ->
        Why3.Hashcons.combine2
          (e_hash c) (e_hash e1) (e_hash e2)
          
  let tag n e = { e with e_tag = n;
                  e_fv = fv_node e.e_node }
end)

(* -------------------------------------------------------------------- *)
let mk_expr e ty =
  Hexpr.hashcons { e_node = e; e_tag = -1; e_fv = fv_node e; e_ty = ty }

let e_int   i       = mk_expr (Eint i) tint
let e_local x ty    = mk_expr (Elocal x) ty
let e_var   x ty    = mk_expr (Evar x) ty
let e_op x targs ty = mk_expr (Eop (x, targs)) ty
let e_let pt e1 e2  = mk_expr (Elet (pt, e1, e2)) e2.e_ty
let e_tuple es      = mk_expr (Etuple es) (ttuple (List.map e_ty es))
let e_if   c e1 e2  = mk_expr (Eif (c, e1, e2)) e2.e_ty

let e_app x args = 
  match x.e_node with
  | Eapp(x', args') -> mk_expr (Eapp (x', (args'@args)))
  | _ -> mk_expr (Eapp (x, args))

(* -------------------------------------------------------------------- *)
let lp_ids = function
  | LSymbol (id,_) -> [id] 
  | LTuple ids -> List.map fst ids

let e_map fty fe e =
  match e.e_node with 
  | Eint _
  | Elocal _
  | Evar _                -> e
  | Eop (p, tys)          -> 
      let tys' = List.smart_map fty tys in
      let ty'  = fty e.e_ty in
      if tys == tys' && e.e_ty == ty' then e else
      e_op p tys' ty'
  | Eapp (e1, args)       -> 
      let e1' = fe e1 in
      let args' = List.smart_map fe args in
      let ty'  = fty e.e_ty in
      if e1 == e1' && args == args' && e.e_ty = ty' then e else 
      e_app e1' args' ty'
  | Elet (lp, e1, e2)     -> 
      let e1' = fe e1 in
      let e2' = fe e2 in 
      if e1 == e1' && e2 == e2' then e else
      e_let lp e1' e2'
  | Etuple le             -> 
      let le' = List.smart_map fe le in
      if le == le' then e else
      e_tuple le'
  | Eif (e1, e2, e3)      -> 
      let e1' = fe e1 in
      let e2' = fe e2 in 
      let e3' = fe e3 in 
      if e1 == e1' && e2 == e2' && e3 = e3' then e else
      e_if e1' e2' e3' 

let rec e_fold fe state e =
  match e.e_node with
  | Eint _                -> state
  | Elocal _              -> state
  | Evar _                -> state
  | Eop _                 -> state
  | Eapp (e, args)        -> List.fold_left fe (fe state e) args
  | Elet (_, e1, e2)      -> List.fold_left fe state [e1; e2]
  | Etuple es             -> List.fold_left fe state es
  | Eif (e1, e2, e3)      -> List.fold_left fe state [e1; e2; e3]

module MSHe = EcMaps.MakeMSH(struct type t = expr let tag e = e.e_tag end)
module Me = MSHe.M  
module Se = MSHe.S
module He = MSHe.H  

(* -------------------------------------------------------------------- *)
let rec expr_dump (e : expr) =
  match e.e_node with
  | _ -> dleaf "expression"

(* -------------------------------------------------------------------- *)

type e_subst = { 
    es_p   : EcPath.path -> EcPath.path;
    es_ty  : ty -> ty;
    es_mp  : EcPath.mpath -> EcPath.mpath; 
    es_loc : expr Mid.t;
  }

let e_subst_id = { 
    es_p   = identity;
    es_ty  = identity;
    es_mp  = identity;
    es_loc = Mid.empty;
 }

let e_subst_init on_path on_ty on_mpath = {
    es_p   = on_path;
    es_ty  = on_ty;
    es_mp  = EcPath.Hm.memo 107 (EcPath.m_subst on_path on_mpath);
    es_loc = Mid.empty;
}
      
let add_local s (x,t) = 
  let x' = EcIdent.fresh x in
  let t' = s.es_ty t in
  let merger o = assert (o = None); Some (e_local x' t') in
  { s with es_loc = Mid.change merger x s.es_loc }, (x',t')

let add_locals = List.map_fold add_local 

let subst_lpattern (s: e_subst) (lp:lpattern) = 
  match lp with
  | LSymbol x ->
      let s, x' = add_local s x in
      s , LSymbol x'
  | LTuple xs ->
      let s',xs'  = add_locals s xs in
      s', LTuple xs'

let rec e_subst (s: e_subst) e =
  match e.e_node with
  | Elocal id -> 
      (try Mid.find id s.es_loc with _ -> 
        (* FIXME : this can be dangerous, maybe use a flag *)
        let ty' = s.es_ty e.e_ty in
        if e.e_ty == ty' then e else e_local id ty')
  | Evar pv -> 
      let pv' = pv_subst s.es_mp pv in
      let ty' = s.es_ty e.e_ty in
      if pv == pv' && e.e_ty == ty' then e 
      else e_var pv' ty'
  | Eop(p,tys) ->
      let p'   = s.es_p p in
      let tys' = List.smart_map s.es_ty tys in
      let ty'  = s.es_ty e.e_ty in
      if p == p' && tys == tys' && e.e_ty == ty' then e else
      e_op p' tys' ty'
  | Elet(lp,e1,e2) -> 
      let e1 = e_subst s e1 in
      let s,lp = subst_lpattern s lp in
      let e2 = e_subst s e2 in
      e_let lp e1 e2
  | _ -> e_map s.es_ty (e_subst s) e
    
let e_mapty onty = 
  e_subst { e_subst_id with es_ty = onty; }

let e_uni (uidmap : ty Muid.t) = e_mapty (Tuni.subst uidmap)


(* -------------------------------------------------------------------- *)
module Dump = struct
  let ty_dump pp =
    let rec ty_dump pp ty = 
      match ty.ty_node with 
      | Tunivar i ->
          EcDebug.single pp ~extra:(string_of_int i) "Tunivar"
  
      | Tvar a ->
          EcDebug.single pp ~extra:(EcIdent.tostring a) "Tvar"
  
      | Ttuple tys ->
          EcDebug.onhlist pp "Ttuple" ty_dump tys
  
      | Tconstr (p, tys) ->
          let strp = EcPath.tostring p in
            EcDebug.onhlist pp ~extra:strp "Tconstr" ty_dump tys
      | Tfun (t1, t2) ->
          EcDebug.onhlist pp "Tfun" ty_dump [t1;t2]
    in
      fun ty -> ty_dump pp ty

  let ex_dump pp =
    let rec ex_dump pp e =
      match e.e_node with
      | Eint i ->
          EcDebug.single pp ~extra:(string_of_int i) "Eint"

      | Elocal x ->
          EcDebug.onhlist pp
            "Elocal" ~extra:(EcIdent.tostring x)
            ty_dump []
        
      | Evar x ->
          EcDebug.onhlist pp
            "Evar" ~extra:(EcPath.m_tostring x.pv_name)
            ty_dump []

      | Eop (x, tys) ->
          EcDebug.onhlist pp "Eop" ~extra:(EcPath.tostring x)
            ty_dump tys
          
      | Eapp (e, args) -> 
          EcDebug.onhlist pp "Eapp" ex_dump (e::args)

      | Elet (_p, e1, e2) ->            (* FIXME *)
          let printers = [ex_dump^~ e1; ex_dump^~ e2] in
            EcDebug.onseq pp "Elet" (Stream.of_list printers)
        
      | Etuple es ->
          EcDebug.onhlist pp ~enum:true "Etuple" ex_dump es
        
      | Eif (c, e1, e2) ->
          EcDebug.onhlist pp "Eif" ex_dump [c; e1; e2]
    in
      fun e -> ex_dump pp e
end
