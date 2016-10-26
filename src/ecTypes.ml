(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcIdent
open EcPath
open EcUid

module BI = EcBigInt

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
let rec dump_ty ty =
  match ty.ty_node with
  | Tglob p ->
      EcPath.m_tostring p

  | Tunivar i ->
      Printf.sprintf "#%d" i

  | Tvar id ->
      EcIdent.tostring id

  | Ttuple tys ->
      Printf.sprintf "(%s)" (String.concat ", " (List.map dump_ty tys))

  | Tconstr (p, tys) ->
      Printf.sprintf "%s[%s]" (EcPath.tostring p)
        (String.concat ", " (List.map dump_ty tys))

  | Tfun (t1, t2) ->
      Printf.sprintf "(%s) -> (%s)" (dump_ty t1) (dump_ty t2)

(* -------------------------------------------------------------------- *)
let tuni uid     = mk_ty (Tunivar uid)
let tvar id      = mk_ty (Tvar id)
let tconstr p lt = mk_ty (Tconstr (p, lt))
let tfun t1 t2   = mk_ty (Tfun (t1, t2))
let tglob m      = mk_ty (Tglob m)

(* -------------------------------------------------------------------- *)
let tunit      = tconstr EcCoreLib.CI_Unit .p_unit  []
let tbool      = tconstr EcCoreLib.CI_Bool .p_bool  []
let tint       = tconstr EcCoreLib.CI_Int  .p_int   []
let tdistr ty  = tconstr EcCoreLib.CI_Distr.p_distr [ty]
let treal      = tconstr EcCoreLib.CI_Real .p_real  []
let tcpred ty  = tfun ty tbool

let ttuple lt    =
  match lt with
  | []  -> tunit
  | [t] -> t
  | _ -> mk_ty (Ttuple lt)

let toarrow dom ty =
  List.fold_right tfun dom ty

let tpred t = tfun t tbool

(* -------------------------------------------------------------------- *)
let tytuple_flat (ty : ty) =
  match ty.ty_node with Ttuple tys -> tys | _ -> [ty]

let rec tyfun_flat (ty : ty) =
  match ty.ty_node with
  | Tfun (t1, t2) ->
      let dom, codom = tyfun_flat t2 in (t1 :: dom, codom)
  | _ ->
      ([], ty)

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
        else match Char.lowercase_ascii x.[i] with
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

(* -------------------------------------------------------------------- *)
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

  let univars =
    let rec doit univars t =
      match t.ty_node with
      | Tunivar uid -> Suid.add uid univars
      | _ -> ty_fold doit univars t

    in fun t -> doit Suid.empty t

  let rec fv_rec fv t =
    match t.ty_node with
    | Tunivar id -> Suid.add id fv
    | _ -> ty_fold fv_rec fv t

  let fv = fv_rec Suid.empty
end

(* -------------------------------------------------------------------- *)
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
  match EcPath.x_compare v1.pv_name v2.pv_name with
  | 0 -> Pervasives.compare v1.pv_kind v2.pv_kind
  | r -> r

let pv_compare_p v1 v2 =
  match EcPath.x_compare_na v1.pv_name v2.pv_name with
  | 0 -> Pervasives.compare v1.pv_kind v2.pv_kind
  | r -> r

let pv_ntr_compare v1 v2 =
  match Pervasives.compare v1.pv_kind v2.pv_kind with
  | 0 -> EcPath.x_ntr_compare v1.pv_name v2.pv_name
  | r -> r

let is_loc  v = match v.pv_kind with PVloc  -> true | _ -> false
let is_glob v = match v.pv_kind with PVglob -> true | _ -> false

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
  { pv_name = EcPath.xqname f s; pv_kind = PVloc }

let pv_arg (f : EcPath.xpath) = pv_loc f "arg"
let pv_res (f : EcPath.xpath) = pv_loc f "res"

let xp_glob x =
  let top = x.EcPath.x_top in
  if top.EcPath.m_args = [] then x else
    (* remove the functor argument *)
    let ntop = EcPath.mpath top.m_top [] in
    EcPath.xpath ntop x.EcPath.x_sub

let pv_glob x =
  { pv_name = xp_glob x; pv_kind = PVglob }

let pv x k =
  match k with
  | PVglob -> pv_glob x
  | PVloc  -> { pv_name = x; pv_kind = k }

let pv_subst m_subst px =
  let mp' = m_subst px.pv_name in
  if px.pv_name == mp' then px else pv mp' px.pv_kind

(* -------------------------------------------------------------------- *)
type lpattern =
  | LSymbol of (EcIdent.t * ty)
  | LTuple  of (EcIdent.t * ty) list
  | LRecord of EcPath.path * (EcIdent.t option * ty) list

let idty_equal (x1,t1) (x2,t2) =
  EcIdent.id_equal x1 x2 && ty_equal t1 t2

let lp_equal p1 p2 =
  match p1, p2 with
  | LSymbol xt1, LSymbol xt2 -> idty_equal xt1 xt2
  | LTuple lx1, LTuple lx2 -> List.all2 idty_equal lx1 lx2
  | _ -> false

let idty_hash (x,t) = Why3.Hashcons.combine (EcIdent.id_hash x) (ty_hash t)

let lp_hash = function
  | LSymbol  x -> idty_hash x
  | LTuple  lx -> Why3.Hashcons.combine_list idty_hash 0 lx

  | LRecord (p, lx) ->
      let for1 (x, ty) =
        Why3.Hashcons.combine (ty_hash ty)
          (Why3.Hashcons.combine_option EcIdent.id_hash x)
      in
        Why3.Hashcons.combine_list for1 (p_hash p) lx

let lp_ids = function
  | LSymbol (id,_)  -> [id]
  | LTuple  ids     -> List.map fst ids
  | LRecord (_,ids) -> List.pmap fst ids

let lp_bind = function
  | LSymbol b     -> [b]
  | LTuple  b     -> b
  | LRecord (_,b) ->
      List.pmap (fun (x, ty) -> omap (fun x -> (x, ty)) x) b

(* -------------------------------------------------------------------- *)
type expr = {
  e_node : expr_node;
  e_ty   : ty;
  e_fv   : int Mid.t;
  e_tag  : int;
}

and expr_node =
  | Eint   of BI.zint                      (* int. literal          *)
  | Elocal of EcIdent.t                    (* let-variables         *)
  | Evar   of prog_var                     (* module variable       *)
  | Eop    of EcPath.path * ty list        (* op apply to type args *)
  | Eapp   of expr * expr list             (* op. application       *)
  | Equant of equantif * ebindings * expr  (* fun/forall/exists     *)
  | Elet   of lpattern * expr * expr       (* let binding           *)
  | Etuple of expr list                    (* tuple constructor     *)
  | Eif    of expr * expr * expr           (* _ ? _ : _             *)
  | Ematch of expr * expr list * ty        (* match _ with _        *)
  | Eproj  of expr * int                   (* projection of a tuple *)

and equantif  = [ `ELambda | `EForall | `EExists ]
and ebinding  = EcIdent.t * ty
and ebindings = ebinding list

type closure = (EcIdent.t * ty) list * expr

(* -------------------------------------------------------------------- *)
let e_equal   = ((==) : expr -> expr -> bool)
let e_hash    = fun e -> e.e_tag
let e_compare = fun e1 e2 -> e_hash e1 - e_hash e2
let e_fv e    = e.e_fv
let e_ty e    = e.e_ty

(* -------------------------------------------------------------------- *)
let lp_fv = function
  | LSymbol (id, _) ->
      Sid.singleton id

  | LTuple ids ->
      List.fold_left (fun s (id, _) -> Sid.add id s) Sid.empty ids

  | LRecord (_, ids) ->
      List.fold_left
        (fun s (id, _) -> ofold Sid.add s id)
        Sid.empty ids

let pv_fv pv = EcPath.x_fv Mid.empty pv.pv_name

let fv_node e =
  let union ex =
    List.fold_left (fun s e -> fv_union s (ex e)) Mid.empty
  in

  match e with
  | Eint _            -> Mid.empty
  | Eop (_, tys)      -> union (fun a -> a.ty_fv) tys
  | Evar v            -> pv_fv v
  | Elocal id         -> fv_singleton id
  | Eapp (e, es)      -> union e_fv (e :: es)
  | Elet (lp, e1, e2) -> fv_union (e_fv e1) (fv_diff (e_fv e2) (lp_fv lp))
  | Etuple es         -> union e_fv es
  | Eif (e1, e2, e3)  -> union e_fv [e1; e2; e3]
  | Ematch (e, es, _) -> union e_fv (e :: es)
  | Equant (_, b, e)  -> List.fold_left (fun s (id, _) -> Mid.remove id s) (e_fv e) b
  | Eproj (e, _)      -> e_fv e

(* -------------------------------------------------------------------- *)
let qt_equal : equantif -> equantif -> bool = (==)
let qt_hash  : equantif -> int = Hashtbl.hash

(* -------------------------------------------------------------------- *)
module Hexpr = Why3.Hashcons.Make (struct
  type t = expr

  let b_equal b1 b2 =
    let b1_equal (x1, ty1) (x2, ty2) =
      EcIdent.id_equal x1 x2 && ty_equal ty1 ty2 in
    List.all2 b1_equal b1 b2

  let equal_node e1 e2 =
    match e1, e2 with
    | Eint   i1, Eint   i2 -> BI.equal i1 i2
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

    | Ematch (e1, es1, ty1), Ematch (e2, es2, ty2) ->
           List.all2 e_equal (e1 :: es1) (e2 :: es2)
        && ty_equal ty1 ty2

    | Equant (q1, b1, e1), Equant (q2, b2, e2) ->
        qt_equal q1 q2 && e_equal e1 e2 && b_equal b1 b2

    | Eproj(e1, i1), Eproj(e2, i2) ->
        i1 = i2 && e_equal e1 e2

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
    | Eint   i -> BI.hash i
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

    | Ematch (e, es, ty) ->
        Why3.Hashcons.combine_list e_hash
          (Why3.Hashcons.combine (e_hash e) (ty_hash ty))
          es

    | Equant (q, b, e) ->
        Why3.Hashcons.combine2 (qt_hash q) (e_hash e) (b_hash b)

    | Eproj (e, i) ->
        Why3.Hashcons.combine (e_hash e) i

  let tag n e =
    let fv = fv_union (fv_node e.e_node) e.e_ty.ty_fv in
      { e with e_tag = n; e_fv = fv; }
end)

(* -------------------------------------------------------------------- *)
let mk_expr e ty =
  Hexpr.hashcons { e_node = e; e_tag = -1; e_fv = Mid.empty; e_ty = ty }

let e_tt    = mk_expr (Eop (EcCoreLib.CI_Unit.p_tt, [])) tunit
let e_int   = fun i -> mk_expr (Eint i) tint
let e_local = fun x ty -> mk_expr (Elocal x) ty
let e_var   = fun x ty -> mk_expr (Evar x) ty
let e_op    = fun x targs ty -> mk_expr (Eop (x, targs)) ty
let e_let   = fun pt e1 e2 -> mk_expr (Elet (pt, e1, e2)) e2.e_ty
let e_tuple = fun es ->
  match es with
  | []  -> e_tt
  | [x] -> x
  | _   -> mk_expr (Etuple es) (ttuple (List.map e_ty es))

let e_if    = fun c e1 e2 -> mk_expr (Eif (c, e1, e2)) e2.e_ty
let e_match = fun e es ty -> mk_expr (Ematch (e, es, ty)) ty
let e_proj  = fun e i ty -> mk_expr (Eproj(e,i)) ty

let e_quantif q b e =
  if List.is_empty b then e else

  let b, e =
    match e.e_node with
    | Equant (q', b', e) when qt_equal q q' -> (b@b', e)
    | _ -> b, e in

  let ty =
    match q with
    | `ELambda -> toarrow (List.map snd b) e.e_ty
    | `EForall | `EExists -> tbool

  in mk_expr (Equant (q, b, e)) ty

let e_forall b e = e_quantif `EForall b e
let e_exists b e = e_quantif `EExists b e
let e_lam    b e = e_quantif `ELambda b e

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

  let l_record (lp, (p, xs)) (p', xs') =
    if p == p' && xs == xs' then lp else LRecord (p', xs')

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

  let e_proj (e, e1, i) (e1', ty') =
    if   e1 == e1' && e.e_ty == ty'
    then e
    else e_proj e1' i ty'

  let e_if (e, (e1, e2, e3)) (e1', e2', e3') =
    if   e1 == e1' && e2 == e2' && e3 == e3'
    then e
    else e_if e1' e2' e3'

  let e_match (e, (b, es, ty)) (b', es', ty') =
    if   b == b' && es == es' && ty == ty'
    then e
    else e_match b es ty

  let e_lam (e, (b, body)) (b', body') =
    if   b == b' && body == body'
    then e
    else e_lam b' body'

  let e_quant (e, (q, b, body)) (q', b', body') =
    if   q == q' && b == b' && body == body'
    then e
    else e_quantif q' b' body'
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

  | Eproj (e1, i) ->
      let e' = fe e1 in
      let ty = fty e.e_ty in
      ExprSmart.e_proj (e,e1,i) (e',ty)

  | Eif (e1, e2, e3) ->
      let e1' = fe e1 in
      let e2' = fe e2 in
      let e3' = fe e3 in
      ExprSmart.e_if (e, (e1, e2, e3)) (e1', e2', e3')

  | Ematch (b, es, ty) ->
      let ty' = fty ty in
      let b'  = fe b in
      let es' = List.Smart.map fe es in
      ExprSmart.e_match (e, (b, es, ty)) (b', es', ty')

  | Equant (q, b, bd) ->
      let dop (x, ty as xty) =
        let ty' = fty ty in
          if ty == ty' then xty else (x, ty') in
      let b'  = List.Smart.map dop b in
      let bd' = fe bd in
      ExprSmart.e_quant (e, (q, b, bd)) (q, b', bd')

let rec e_fold fe state e =
  match e.e_node with
  | Eint _                -> state
  | Elocal _              -> state
  | Evar _                -> state
  | Eop _                 -> state
  | Eapp (e, args)        -> List.fold_left fe (fe state e) args
  | Elet (_, e1, e2)      -> List.fold_left fe state [e1; e2]
  | Etuple es             -> List.fold_left fe state es
  | Eproj(e,_)            -> fe state e
  | Eif (e1, e2, e3)      -> List.fold_left fe state [e1; e2; e3]
  | Ematch (e, es, _)     -> List.fold_left fe state (e :: es)
  | Equant (_, _, e1)     -> fe state e1

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

(* -------------------------------------------------------------------- *)
let is_e_subst_id s =
  not s.es_freshen && s.es_p == identity &&
    s.es_ty == identity && s.es_mp == identity &&
    s.es_xp == identity && Mid.is_empty s.es_loc

(* -------------------------------------------------------------------- *)
let e_subst_init freshen on_path on_ty opdef on_mpath esloc =
  let on_mp =
    let f = EcPath.m_subst on_path on_mpath in
    if f == identity then f else EcPath.Hm.memo 107 f in
  let on_xp =
    let f = EcPath.x_subst on_mp in
    if f == identity then f else EcPath.Hx.memo 107 f in

  { es_freshen = freshen;
    es_p       = on_path;
    es_ty      = on_ty;
    es_opdef   = opdef;
    es_mp      = on_mp;
    es_xp      = on_xp;
    es_loc     = esloc; }

(* -------------------------------------------------------------------- *)
let add_local s ((x, t) as xt) =
  let x' = if s.es_freshen then EcIdent.fresh x else x in
  let t' = s.es_ty t in

    if   x == x' && t == t'
    then (s, xt)
    else
      let merger o = assert (o = None); Some (e_local x' t') in
        ({ s with es_loc = Mid.change merger x s.es_loc }, (x', t'))

(* -------------------------------------------------------------------- *)
let add_locals = List.Smart.map_fold add_local

(* -------------------------------------------------------------------- *)
let subst_lpattern (s: e_subst) (lp:lpattern) =
  match lp with
  | LSymbol x ->
      let (s, x') = add_local s x in
        (s, ExprSmart.l_symbol (lp, x) x')

  | LTuple xs ->
      let (s, xs') = add_locals s xs in
        (s, ExprSmart.l_tuple (lp, xs) xs')

  | LRecord (p, xs) ->
      let (s, xs') =
        List.Smart.map_fold
          (fun s ((x, t) as xt) ->
            match x with
            | None ->
                let t' = s.es_ty t in
                  if t == t' then (s, xt) else (s, (x, t'))
            | Some x ->
                let (s, (x', t')) = add_local s (x, t) in
                  if   x == x' && t == t'
                  then (s, xt)
                  else (s, (Some x', t')))
          s xs
      in
        (s, ExprSmart.l_record (lp, (p, xs)) (s.es_p p, xs'))

(* -------------------------------------------------------------------- *)
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

  | Equant (q, b, e1) ->
      let s, b' = add_locals s b in
      let e1' = e_subst s e1 in
        ExprSmart.e_quant (e, (q, b, e1)) (q, b', e1')

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
    | Equant (`ELambda, largs, lbody) when args <> [] ->
        let largs1, largs2 = List.takedrop (List.length args  ) largs in
        let  args1,  args2 = List.takedrop (List.length largs1)  args in
          (Mid.of_list (List.combine (List.map fst largs1) args1),
           args2, e_lam largs2 lbody)

    | _ -> (Mid.of_list [], args, e)
  in

  let sag = { e_subst_id with es_loc = sag } in
    e_app (e_subst sag e) args ety

(* -------------------------------------------------------------------- *)
let e_subst_closure s (args, e) =
  let (s, args) = add_locals s args in
    (args, e_subst s e)

(* -------------------------------------------------------------------- *)
let e_subst s =
  if is_e_subst_id s then identity
  else
    if s.es_freshen then e_subst s
    else He.memo 107 (e_subst s)

(* -------------------------------------------------------------------- *)
let e_mapty onty =
  e_subst { e_subst_id with es_ty = onty; }

(* -------------------------------------------------------------------- *)
let e_uni uidmap =
  e_mapty (Tuni.offun uidmap)

(* -------------------------------------------------------------------- *)
let is_local e =
  match e.e_node with
  | Elocal _ -> true
  | _ -> false

(* -------------------------------------------------------------------- *)
let destr_local e =
   match e.e_node with
  | Elocal id -> id
  | _ -> assert false

(* -------------------------------------------------------------------- *)
let is_var e =
  match e.e_node with
  | Evar _ -> true
  | _ -> false

(* -------------------------------------------------------------------- *)
let destr_var e =
   match e.e_node with
  | Evar pv -> pv
  | _ -> assert false

(* -------------------------------------------------------------------- *)
let is_tuple_var e =
  match e.e_node with
  | Etuple es -> List.for_all is_var es
  | _ -> false

(* -------------------------------------------------------------------- *)
let destr_tuple_var e =
   match e.e_node with
  | Etuple es -> List.map destr_var es
  | _ -> assert false
