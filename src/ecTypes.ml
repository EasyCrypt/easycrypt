(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcIdent
open EcPath
open EcUid

(* -------------------------------------------------------------------- *)
type ty = {
  ty_node : ty_node;
  ty_fv   : int EcIdent.Mid.t; (* only ident appearing in path *)
  ty_tag  : int;
}

and ty_node =
  | Tglob   of EcPath.mpath (* The tuple of global variable of the module *)
  | Tunivar of EcUid.uid
  | Tvar    of EcIdent.t 
  | Ttuple  of ty list
  | Tconstr of EcPath.path * ty list
  | Tfun    of ty * ty

type dom = ty list

let ty_equal : ty -> ty -> bool = (==)
let ty_hash ty = ty.ty_tag

module Hsty = Why3.Hashcons.Make (struct
  type t = ty

  let equal ty1 ty2 =
    match ty1.ty_node, ty2.ty_node with
    | Tglob m1, Tglob m2 ->
        EcPath.m_equal m1 m2 

    | Tunivar u1, Tunivar u2 -> 
        uid_equal u1 u2

    | Tvar v1, Tvar v2 -> 
        id_equal v1 v2

    | Ttuple lt1, Ttuple lt2 -> 
        List.all2 ty_equal lt1 lt2

    | Tconstr (p1, lt1), Tconstr (p2, lt2) -> 
        EcPath.p_equal p1 p2 && List.all2 ty_equal lt1 lt2

    | Tfun (d1, c1), Tfun (d2, c2)-> 
        ty_equal d1 d2 && ty_equal c1 c2

    | _, _ -> false
      
  let hash ty = 
    match ty.ty_node with 
    | Tglob m          -> EcPath.m_hash m
    | Tunivar u        -> u
    | Tvar    id       -> EcIdent.tag id
    | Ttuple  tl       -> Why3.Hashcons.combine_list ty_hash 0 tl
    | Tconstr (p, tl)  -> Why3.Hashcons.combine_list ty_hash p.p_tag tl
    | Tfun    (t1, t2) -> Why3.Hashcons.combine (ty_hash t1) (ty_hash t2)
        
  let fv ty =
    let union ex =
      List.fold_left (fun s a -> fv_union s (ex a)) Mid.empty in

    match ty with
    | Tglob m          -> EcPath.m_fv Mid.empty m
    | Tunivar _        -> Mid.empty
    | Tvar    _        -> Mid.empty
    | Ttuple  tys      -> union (fun a -> a.ty_fv) tys
    | Tconstr (_, tys) -> union (fun a -> a.ty_fv) tys
    | Tfun    (t1, t2) -> union (fun a -> a.ty_fv) [t1; t2]

  let tag n ty = { ty with ty_tag = n; ty_fv = fv ty.ty_node; }
end)

let mk_ty node =  
  Hsty.hashcons { ty_node = node; ty_tag = -1; ty_fv = Mid.empty }

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

let ttuple lt    = 
  match lt with
  | [t] -> t
  | _ -> mk_ty (Ttuple lt)

let tconstr p lt = mk_ty (Tconstr(p,lt))
let tfun t1 t2   = mk_ty (Tfun(t1,t2)) 
let tglob m      = mk_ty (Tglob m)

(* -------------------------------------------------------------------- *)
let tunit      = tconstr EcCoreLib.p_unit  []
let tbool      = tconstr EcCoreLib.p_bool  []
let tint       = tconstr EcCoreLib.p_int   []
let tdistr ty  = tconstr EcCoreLib.p_distr [ty]
let tfset  ty  = tconstr EcCoreLib.p_fset  [ty]
let tcpred ty  = tconstr EcCoreLib.p_cpred [ty]
let treal      = tconstr EcCoreLib.p_real  []
 
let toarrow dom ty = 
  List.fold_right tfun dom ty

let flatten_ty (ty : ty) =
  match ty with
  | { ty_node = Ttuple tys } -> tys
  | _ -> [ty]

(* -------------------------------------------------------------------- *)
module TySmart = struct
  let tglob (ty, mp) (mp') =
    if mp == mp' then ty else tglob mp'

  let ttuple (ty, tys) (tys') =
    if tys == tys' then ty else ttuple tys'

  let tconstr (ty, (lp, tys)) (lp', tys') =
    if lp == lp' && tys == tys' then ty else tconstr lp' tys'

  let tfun (ty, (t1, t2)) (t1', t2') =
    if t1 == t1' && t2 == t2' then ty else tfun t1' t2'
end

(* -------------------------------------------------------------------- *)
let ty_map f t = 
  match t.ty_node with 
  | Tglob _ | Tunivar _ | Tvar _ -> t

  | Ttuple lty -> 
      TySmart.ttuple (t, lty) (List.Smart.map f lty)

  | Tconstr (p, lty) -> 
      let lty' = List.Smart.map f lty in
        TySmart.tconstr (t, (p, lty)) (p, lty')

  | Tfun (t1, t2) -> 
      TySmart.tfun (t, (t1, t2)) (f t1, f t2)

let ty_fold f s ty = 
  match ty.ty_node with 
  | Tglob _ | Tunivar _ | Tvar _ -> s
  | Ttuple lty -> List.fold_left f s lty
  | Tconstr(_, lty) -> List.fold_left f s lty
  | Tfun(t1,t2) -> f (f s t1) t2

let ty_sub_exists f t =
  match t.ty_node with
  | Tglob _ | Tunivar _ | Tvar _ -> false
  | Ttuple lty -> List.exists f lty
  | Tconstr (_, lty) -> List.exists f lty
  | Tfun (t1, t2) -> f t1 || f t2

let ty_iter f t = 
  match t.ty_node with
  | Tglob _ | Tunivar _ | Tvar _ -> ()
  | Ttuple lty -> List.iter f lty
  | Tconstr (_, lty) -> List.iter f lty
  | Tfun (t1,t2) -> f t1; f t2

exception FoundUnivar

let rec ty_check_uni t = 
  match t.ty_node with
  | Tunivar _ -> raise FoundUnivar
  | _ -> ty_iter ty_check_uni t

(* -------------------------------------------------------------------- *)
let symbol_of_ty (ty : ty) =
  match ty.ty_node with
  | Tglob   _      -> "g"
  | Tunivar _      -> "u"
  | Tvar    _      -> "x"
  | Ttuple  _      -> "x"
  | Tfun    _      -> "f"
  | Tconstr (p, _) ->
      let x = EcPath.basename p in
      let rec doit i =
        if   i >= String.length x
        then "x"
        else match Char.lowercase x.[i] with
             | 'a' .. 'z' -> String.make 1 x.[i]
             | _ -> doit (i+1)
      in
        doit 0

let fresh_id_of_ty (ty : ty) =
  EcIdent.create (symbol_of_ty ty)

(* -------------------------------------------------------------------- *)
type ty_subst = {
  ts_p   : EcPath.path -> EcPath.path;
  ts_mp  : EcPath.mpath -> EcPath.mpath;
  ts_def : (EcIdent.t list * ty) EcPath.Mp.t;
  ts_u   : EcUid.uid -> ty option;
  ts_v   : EcIdent.t -> ty option;
}

let ty_subst_id = 
  { ts_p   = identity;
    ts_mp  = identity;
    ts_def = Mp.empty;
    ts_u   = funnone ;
    ts_v   = funnone ; }

let is_ty_subst_id s = 
     s.ts_p  == identity
  && s.ts_mp == identity
  && s.ts_u  == funnone
  && s.ts_v  == funnone
  && Mp.is_empty s.ts_def

let rec ty_subst s =
  if is_ty_subst_id s then identity
  else
    Hty.memo_rec 107 (fun aux ty ->
      match ty.ty_node with 
      | Tglob m       -> TySmart.tglob (ty, m) (s.ts_mp m)
      | Tunivar id    -> odfl ty (s.ts_u id)
      | Tvar id       -> odfl ty (s.ts_v id)
      | Ttuple lty    -> TySmart.ttuple (ty, lty) (List.Smart.map aux lty)
      | Tfun (t1, t2) -> TySmart.tfun (ty, (t1, t2)) (aux t1, aux t2)

      | Tconstr(p, lty) -> begin
        match Mp.find_opt p s.ts_def with
        | None -> 
            let p'   = s.ts_p p in
            let lty' = List.Smart.map aux lty in
              TySmart.tconstr (ty, (p, lty)) (p', lty')

        | Some (args, body) ->
            let s =
              try  Mid.of_list (List.combine args (List.map aux lty))
              with Failure _ -> assert false
            in
              ty_subst { ty_subst_id with ts_v = Mid.find_opt^~ s; } body
      end)

module Tuni = struct
  let offun uidmap =
    ty_subst { ty_subst_id with ts_u = uidmap }

  let offun_dom uidmap dom =
    List.map (offun uidmap) dom

  let subst (uidmap : ty Muid.t) =
    ty_subst { ty_subst_id with ts_u = Muid.find_opt^~ uidmap } 

  let subst1 ((id, t) : uid * ty) =
    subst (Muid.singleton id t)

  let subst_dom uidmap dom =
    List.map (subst uidmap) dom 

  let occurs u = 
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

end

module Tvar = struct 
  let subst (s : ty Mid.t) =
    ty_subst { ty_subst_id with ts_v = Mid.find_opt^~ s }

  let subst1 (id,t) = 
    subst (Mid.singleton id t)

  let init lv lt = 
    assert (List.length lv = List.length lt);
    List.fold_left2 (fun s v t -> Mid.add v t s) Mid.empty lv lt

  let rec fv_rec fv t = 
    match t.ty_node with
    | Tvar id -> Sid.add id fv 
    | _ -> ty_fold fv_rec fv t 

  let fv = fv_rec Sid.empty

end

(* -------------------------------------------------------------------- *)
type pvar_kind = 
  | PVglob
  | PVloc 

type prog_var = {
  pv_name : EcPath.xpath;
  pv_kind : pvar_kind;
}

let pv_equal v1 v2 = 
  EcPath.x_equal v1.pv_name v2.pv_name && v1.pv_kind = v2.pv_kind 

let pv_hash v = 
  Why3.Hashcons.combine (EcPath.x_hash v.pv_name)
    (if v.pv_kind = PVglob then 1 else 0)

let pv_compare v1 v2 = 
  let r = EcPath.x_compare v1.pv_name v2.pv_name in
  if r = 0 then Pervasives.compare v1.pv_kind v2.pv_kind
  else r 

let pv_compare_p v1 v2 =
  let r = EcPath.x_compare_na v1.pv_name v2.pv_name in
  if r = 0 then Pervasives.compare v1.pv_kind v2.pv_kind 
  else r

let is_loc v = match v.pv_kind with PVloc -> true | _ -> false
let is_glob v = match v.pv_kind with PVglob -> true | _ -> false
  
let pv_subst m_subst pv = 
  let mp' = m_subst pv.pv_name in
  if pv.pv_name == mp' then pv else { pv with pv_name = mp'}

let symbol_of_pv pv = 
  EcPath.basename pv.pv_name.EcPath.x_sub

let string_of_pvar_kind = function
  | PVglob -> "PVglob"
  | PVloc  -> "PVloc"

let string_of_pvar (p : prog_var) =
  Printf.sprintf "%s[%s]"
    (EcPath.x_tostring p.pv_name)
    (string_of_pvar_kind p.pv_kind)

(* Notice: global variables are never suspended, local are since they
 * contain the path of the function. *)
    
let pv_loc f s = 
  { pv_name = EcPath.xqname f s;
    pv_kind = PVloc }

let pv_res (f:EcPath.xpath) = pv_loc f "res"

let pv_glob x =
  let top = x.EcPath.x_top in
  let x = 
    if top.EcPath.m_args = [] then x
    else 
      let ntop = EcPath.mpath top.m_top [] in (* remove the functor argument *)
      EcPath.xpath ntop x.EcPath.x_sub in
  { pv_name = x; pv_kind = PVglob }

let pv x k = 
  if k = PVglob then pv_glob x 
  else { pv_name = x; pv_kind = k }

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

let lp_ids = function
  | LSymbol (id,_) -> [id] 
  | LTuple ids -> List.map fst ids

let lp_bind = function
  | LSymbol b -> [b] 
  | LTuple b -> b

(* -------------------------------------------------------------------- *)
type expr = {
  e_node : expr_node;
  e_ty   : ty;
  e_fv   : int Mid.t; 
  e_tag  : int;
}

and expr_node =
  | Elam   of (EcIdent.t * ty) list * expr (* lambda expression *)
  | Eint   of int                          (* int. literal          *)
  | Elocal of EcIdent.t                    (* let-variables         *)
  | Evar   of prog_var                     (* module variable       *)
  | Eop    of EcPath.path * ty list        (* op apply to type args *)
  | Eapp   of expr * expr list             (* op. application       *)
  | Elet   of lpattern * expr * expr       (* let binding           *)
  | Etuple of expr list                    (* tuple constructor     *)
  | Eif    of expr * expr * expr           (* _ ? _ : _             *)

type closure = (EcIdent.t * ty) list * expr

(* -------------------------------------------------------------------- *)
let e_equal   = ((==) : expr -> expr -> bool)
let e_hash    = fun e -> e.e_tag
let e_compare = fun e1 e2 -> e_hash e1 - e_hash e2
let e_fv e    = e.e_fv 
let e_ty e    = e.e_ty

(* -------------------------------------------------------------------- *)
let lp_fv = function
  | LSymbol (id,_) -> Sid.singleton id
  | LTuple ids -> 
      List.fold_left (fun s (id,_) -> Sid.add id s) Sid.empty ids

let pv_fv pv = EcPath.x_fv Mid.empty pv.pv_name

let fv_node e =
  let union ex =
    List.fold_left (fun s e -> fv_union s (ex e)) Mid.empty in

  match e with
  | Eint _            -> Mid.empty
  | Eop (_, tys)      -> union (fun a -> a.ty_fv) tys
  | Evar v            -> pv_fv v 
  | Elocal id         -> fv_singleton id 
  | Eapp (e, es)      -> union e_fv (e :: es)
  | Elet (lp, e1, e2) -> fv_union (e_fv e1) (fv_diff (e_fv e2) (lp_fv lp))
  | Etuple es         -> union e_fv es
  | Eif (e1, e2, e3)  -> union e_fv [e1; e2; e3]
  | Elam (b, e)       -> List.fold_left
                           (fun s (id, _) -> Mid.remove id s)
                           (e_fv e) b

(* -------------------------------------------------------------------- *)
module Hexpr = Why3.Hashcons.Make (struct 
  type t = expr

  let b_equal b1 b2 =
    let b1_equal (x1, ty1) (x2, ty2) = 
      EcIdent.id_equal x1 x2 && ty_equal ty1 ty2 in
    List.all2 b1_equal b1 b2
 
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
    | Elam(b1,e1), Elam(b2,e2) ->
      e_equal e1 e2 && b_equal b1 b2
    | _, _ -> false

  let equal e1 e2 = 
    equal_node e1.e_node e2.e_node && 
    ty_equal e1.e_ty e2.e_ty 

  let b_hash bs =
    let b1_hash (x, ty) = 
      Why3.Hashcons.combine (EcIdent.tag x) (ty_hash ty)
    in
    Why3.Hashcons.combine_list b1_hash 0 bs

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

    | Elam(b,e) ->
        Why3.Hashcons.combine (e_hash e) (b_hash b) 
          
  let tag n e = 
    let fv = fv_union (fv_node e.e_node) e.e_ty.ty_fv in
      { e with e_tag = n; e_fv = fv; }
end)

(* -------------------------------------------------------------------- *)
let mk_expr e ty =
  Hexpr.hashcons { e_node = e; e_tag = -1; e_fv = Mid.empty; e_ty = ty }

let e_tt    = mk_expr (Eop (EcCoreLib.p_tt, [])) tunit
let e_int   = fun i -> mk_expr (Eint i) tint
let e_local = fun x ty -> mk_expr (Elocal x) ty
let e_var   = fun x ty -> mk_expr (Evar x) ty
let e_op    = fun x targs ty -> mk_expr (Eop (x, targs)) ty
let e_let   = fun pt e1 e2 -> mk_expr (Elet (pt, e1, e2)) e2.e_ty
let e_tuple = fun es -> mk_expr (Etuple es) (ttuple (List.map e_ty es))
let e_if    = fun c e1 e2 -> mk_expr (Eif (c, e1, e2)) e2.e_ty

let e_lam b e =
  if b = [] then e
  else 
    let b, e = 
      match e.e_node with
      | Elam(b',e) -> b@b',e
      | _ -> b, e in
    let ty = toarrow (List.map snd b) e.e_ty in
    mk_expr (Elam(b,e)) ty

let e_app x args ty = 
  if args = [] then x 
  else
    match x.e_node with
    | Eapp(x', args') -> mk_expr (Eapp (x', (args'@args))) ty
    | _ -> mk_expr (Eapp (x, args)) ty

(* -------------------------------------------------------------------- *)
module ExprSmart = struct
  let l_symbol (lp, x) x' =
    if x == x' then lp else LSymbol x'

  let l_tuple (lp, xs) xs' =
    if xs == xs' then lp else LTuple xs'

  let e_local (e, (x, ty)) (x', ty') =
    if   x == x' && ty == ty'
    then e
    else e_local x' ty'

  let e_var (e, (pv, ty)) (pv', ty') =
    if   pv == pv' && ty == ty'
    then e
    else e_var pv' ty'

  let e_op (e, (p, tys, ty)) (p', tys', ty') =
    if   p == p' && tys == tys' && ty == ty'
    then e
    else e_op p' tys' ty'

  let e_app (e, (x, args, ty)) (x', args', ty') =
    if   x == x' && args == args' && ty == ty'
    then e
    else e_app x' args' ty'

  let e_let (e, (lp, e1, e2)) (lp', e1', e2') =
    if   lp == lp' && e1 == e1' && e2 == e2'
    then e
    else e_let lp' e1' e2'

  let e_tuple (e, es) es' =
    if es == es' then e else e_tuple es'

  let e_if (e, (e1, e2, e3)) (e1', e2', e3') =
    if   e1 == e1' && e2 == e2' && e3 == e3'
    then e
    else e_if e1' e2' e3'

  let e_lam (e, (b, body)) (b', body') =
    if   b == b' && body == body'
    then e
    else e_lam b' body'
end

let e_map fty fe e =
  match e.e_node with 
  | Eint _ | Elocal _ | Evar _ -> e

  | Eop (p, tys) -> 
      let tys' = List.Smart.map fty tys in
      let ty'  = fty e.e_ty in
        ExprSmart.e_op (e, (p, tys, e.e_ty)) (p, tys', ty')

  | Eapp (e1, args) -> 
      let e1'   = fe e1 in
      let args' = List.Smart.map fe args in
      let ty'   = fty e.e_ty in
        ExprSmart.e_app (e, (e1, args, e.e_ty)) (e1', args', ty')

  | Elet (lp, e1, e2) -> 
      let e1' = fe e1 in
      let e2' = fe e2 in
        ExprSmart.e_let (e, (lp, e1, e2)) (lp, e1', e2')

  | Etuple le -> 
      let le' = List.Smart.map fe le in
        ExprSmart.e_tuple (e, le) le'

  | Eif (e1, e2, e3)      -> 
      let e1' = fe e1 in
      let e2' = fe e2 in 
      let e3' = fe e3 in
        ExprSmart.e_if (e, (e1, e2, e3)) (e1', e2', e3')

  | Elam(b, bd) ->
      let dop (x, ty as xty) =
        let ty' = fty ty in
          if ty == ty' then xty else (x, ty') in
      let b'  = List.Smart.map dop b in
      let bd' = fe bd in
        ExprSmart.e_lam (e, (b, bd)) (b', bd')

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
  | Elam(_,e1)            -> fe state e1

module MSHe = EcMaps.MakeMSH(struct type t = expr let tag e = e.e_tag end)
module Me = MSHe.M  
module Se = MSHe.S
module He = MSHe.H  

(* -------------------------------------------------------------------- *)
type e_subst = { 
    es_freshen : bool; (* true means realloc local *)
    es_p       : EcPath.path -> EcPath.path;
    es_ty      : ty -> ty;
    es_opdef   : (EcIdent.t list * expr) EcPath.Mp.t;
    es_mp      : EcPath.mpath -> EcPath.mpath; 
    es_xp      : EcPath.xpath -> EcPath.xpath;
    es_loc     : expr Mid.t;
  }

let e_subst_id = { 
    es_freshen = false;
    es_p       = identity;
    es_ty      = identity;
    es_opdef   = Mp.empty;
    es_mp      = identity;
    es_xp      = identity;
    es_loc     = Mid.empty;
 }

let e_subst_init freshen on_path on_ty opdef on_mpath = 
  let on_mp = 
    let f = EcPath.m_subst on_path on_mpath in
    if f == identity then f else EcPath.Hm.memo 107 f in
  let on_xp = 
    let f = EcPath.x_subst on_mp in
    if f == identity then f else EcPath.Hx.memo 107 f in
  {
    es_freshen = freshen;
    es_p       = on_path;
    es_ty      = on_ty;
    es_opdef   = opdef;
    es_mp      = on_mp;
    es_xp      = on_xp;
    es_loc     = Mid.empty;
  }
  
let add_local s (x,t as xt) = 
  let x' = if s.es_freshen then EcIdent.fresh x else x in
  let t' = s.es_ty t in
  if x == x' && t == t' then s, xt
  else 
    let merger o = assert (o = None); Some (e_local x' t') in
    { s with es_loc = Mid.change merger x s.es_loc }, (x',t')
      
let add_locals = List.Smart.map_fold add_local

let subst_lpattern (s: e_subst) (lp:lpattern) = 
  match lp with
  | LSymbol x ->
      let (s, x') = add_local s x in
        (s, ExprSmart.l_symbol (lp, x) x')

  | LTuple xs ->
      let (s, xs') = add_locals s xs in
        (s, ExprSmart.l_tuple (lp, xs) xs')

let rec e_subst (s: e_subst) e =
  match e.e_node with
  | Elocal id -> begin
      match Mid.find_opt id s.es_loc with
      | Some e' -> e'
      | None    ->
        assert (not s.es_freshen);
        ExprSmart.e_local (e, (id, e.e_ty)) (id, s.es_ty e.e_ty)
  end

  | Evar pv -> 
      let pv' = pv_subst s.es_xp pv in
      let ty' = s.es_ty e.e_ty in
        ExprSmart.e_var (e, (pv, e.e_ty)) (pv', ty')

  | Eapp ({ e_node = Eop (p, tys) }, args) when Mp.mem p s.es_opdef ->
      let tys  = List.Smart.map s.es_ty tys in
      let ty   = s.es_ty e.e_ty in
      let body = oget (Mp.find_opt p s.es_opdef) in
        e_subst_op ty tys (List.map (e_subst s) args) body

  | Eop (p, tys) when Mp.mem p s.es_opdef ->
      let tys  = List.Smart.map s.es_ty tys in
      let ty   = s.es_ty e.e_ty in
      let body = oget (Mp.find_opt p s.es_opdef) in
        e_subst_op ty tys [] body

  | Eop (p, tys) ->
      let p'   = s.es_p p in
      let tys' = List.Smart.map s.es_ty tys in
      let ty'  = s.es_ty e.e_ty in
        ExprSmart.e_op (e, (p, tys, e.e_ty)) (p', tys', ty')

  | Elet (lp, e1, e2) -> 
      let e1' = e_subst s e1 in
      let s, lp' = subst_lpattern s lp in
      let e2' = e_subst s e2 in
        ExprSmart.e_let (e, (lp, e1, e2)) (lp', e1', e2')

  | Elam (b, e1) ->
    let s, b' = add_locals s b in
    let e1' = e_subst s e1 in
      ExprSmart.e_lam (e, (b, e1)) (b', e1')

  | _ -> e_map s.es_ty (e_subst s) e

and e_subst_op ety tys args (tyids, e) =
  (* FIXME: factor this out *)
  (* FIXME: is es_freshen value correct? *)

  let e =
    let sty = Tvar.init tyids tys in
    let sty = ty_subst { ty_subst_id with ts_v = Mid.find_opt^~ sty; } in
    let sty = { e_subst_id with
                  es_freshen = true;
                  es_ty      = sty } in
      e_subst sty e
  in

  let (sag, args, e) =
    match e.e_node with
    | Elam (largs, lbody) when args <> [] ->
        let largs1, largs2 = List.take_n (List.length args  ) largs in
        let  args1,  args2 = List.take_n (List.length largs1)  args in
          (Mid.of_list (List.combine (List.map fst largs1) args1),
           args2, e_lam largs2 lbody)

    | _ -> (Mid.of_list [], args, e)
  in

  let sag = { e_subst_id with es_loc = sag } in
    e_app (e_subst sag e) args ety

let e_subst_closure s (args, e) =
  let (s, args) = add_locals s args in
    (args, e_subst s e)

let is_subst_id s = 
  not s.es_freshen && s.es_p == identity && 
    s.es_ty == identity && s.es_mp == identity && 
    s.es_xp == identity && Mid.is_empty s.es_loc 

let e_subst s =
  if is_subst_id s then identity
  else 
    if s.es_freshen then e_subst s 
    else He.memo 107 (e_subst s)

let e_mapty onty = 
  e_subst { e_subst_id with es_ty = onty; }

let e_uni uidmap =
  e_mapty (Tuni.offun uidmap)

let is_var e = 
  match e.e_node with
  | Evar _ -> true
  | _ -> false

let destr_var e = 
   match e.e_node with
  | Evar pv -> pv
  | _ -> assert false

let is_tuple_var e = 
  match e.e_node with
  | Etuple es -> List.for_all is_var es
  | _ -> false

let destr_tuple_var e = 
   match e.e_node with
  | Etuple es -> List.map destr_var es
  | _ -> assert false

let proj_distr_ty ty = match ty.ty_node with
  | Tconstr(_,lty) when List.length lty = 1  -> 
    List.hd lty
  | _ -> assert false (* FIXME *)
