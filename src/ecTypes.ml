(* -------------------------------------------------------------------- *)
open EcUtils
open EcIdent
open EcPath
open EcUid

module BI = EcBigInt

(* -------------------------------------------------------------------- *)
type locality  = [`Local | `Declare | `Global]
type is_local  = [`Local | `Global]

let local_of_locality = function
  | `Local   -> `Local
  | `Global  -> `Global
  | `Declare -> `Local

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
    | Tvar    _        -> Mid.empty (* FIXME: section *)
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
let tunit      = tconstr EcCoreLib.CI_Unit .p_unit    []
let tbool      = tconstr EcCoreLib.CI_Bool .p_bool    []
let tint       = tconstr EcCoreLib.CI_Int  .p_int     []
let txint      = tconstr EcCoreLib.CI_xint .p_xint    []

let tdistr ty  = tconstr EcCoreLib.CI_Distr.p_distr   [ty]
let toption ty = tconstr EcCoreLib.CI_Option.p_option [ty]
let treal      = tconstr EcCoreLib.CI_Real .p_real    []
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
let as_tdistr (ty : ty) =
  match ty.ty_node with
  | Tconstr (p, [sty])
      when EcPath.p_equal p EcCoreLib.CI_Distr.p_distr
    -> Some sty

  | _ -> None

let is_tdistr (ty : ty) = as_tdistr ty <> None

(* -------------------------------------------------------------------- *)
let ty_map f t =
  match t.ty_node with
  | Tglob _ | Tunivar _ | Tvar _ -> t

  | Ttuple lty ->
     ttuple (List.Smart.map f lty)

  | Tconstr (p, lty) ->
     let lty = List.Smart.map f lty in
     tconstr p lty

  | Tfun (t1, t2) ->
      tfun (f t1) (f t2)

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
  ts_mp  : EcPath.smsubst;
  ts_def : (EcIdent.t list * ty) EcPath.Mp.t;
  ts_u   : EcUid.uid -> ty option;
  ts_v   : EcIdent.t -> ty option;
}

let ty_subst_id =
  { ts_p   = identity;
    ts_mp  = EcPath.sms_identity;
    ts_def = Mp.empty;
    ts_u   = funnone ;
    ts_v   = funnone ; }

let is_ty_subst_id s =
     s.ts_p  == identity
  && EcPath.sms_is_identity s.ts_mp
  && s.ts_u  == funnone
  && s.ts_v  == funnone
  && Mp.is_empty s.ts_def

let rec ty_subst s =
  if is_ty_subst_id s then identity
  else
    Hty.memo_rec 107 (fun aux ty ->
      match ty.ty_node with
      | Tglob m       -> tglob (EcPath.m_subst s.ts_mp m)
      | Tunivar id    -> odfl ty (s.ts_u id)
      | Tvar id       -> odfl ty (s.ts_v id)
      | Ttuple lty    -> ttuple (List.Smart.map aux lty)
      | Tfun (t1, t2) -> tfun (aux t1) (aux t2)

      | Tconstr(p, lty) -> begin
        match Mp.find_opt p s.ts_def with
        | None ->
            let p   = s.ts_p p in
            let lty = List.Smart.map aux lty in
              tconstr p lty

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
type ovariable = {
  ov_name : EcSymbols.symbol option;
  ov_type : ty;
}

let ov_name { ov_name = x } = x
let ov_type { ov_type = x } = x

let ov_hash v =
  Why3.Hashcons.combine
    (Hashtbl.hash v.ov_name)
    (ty_hash v.ov_type)

let ov_equal vd1 vd2 =
  EcUtils.opt_equal (=) vd1.ov_name vd2.ov_name &&
  ty_equal vd1.ov_type vd2.ov_type

type variable = {
  v_name : EcSymbols.symbol;   (* can be "_" *)
  v_type : ty;
}

let v_name { v_name = x } = x
let v_type { v_type = x } = x

let v_hash v =
  Why3.Hashcons.combine
    (Hashtbl.hash v.v_name)
    (ty_hash v.v_type)

let v_equal vd1 vd2 =
  vd1.v_name = vd2.v_name &&
  ty_equal vd1.v_type vd2.v_type

let ovar_of_var { v_name = n; v_type = t } =
  { ov_name = Some n; ov_type = t }

let ty_fv_and_tvar (ty : ty) =
  EcIdent.fv_union ty.ty_fv (Mid.map (fun () -> 1) (Tvar.fv ty))

(* -------------------------------------------------------------------- *)
type pvar_kind =
  | PVKglob
  | PVKloc

type prog_var =
  | PVglob of EcPath.xpath
  | PVloc of EcSymbols.symbol

let pv_equal v1 v2 = match v1, v2 with
  | PVglob x1, PVglob x2 ->
    EcPath.x_equal x1 x2
  | PVloc i1, PVloc i2 -> EcSymbols.sym_equal i1 i2
  | PVloc _, PVglob _ | PVglob _, PVloc _ -> false

let pv_kind = function
  | PVglob _ -> PVKglob
  | PVloc _ -> PVKloc

let pv_hash v =
  let h = match v with
    | PVglob x -> EcPath.x_hash x
    | PVloc i -> Hashtbl.hash i in

  Why3.Hashcons.combine
    h (if pv_kind v = PVKglob then 1 else 0)

let pv_compare v1 v2 =
  match v1, v2 with
  | PVloc i1,  PVloc i2  -> EcSymbols.sym_compare i1 i2
  | PVglob x1, PVglob x2 -> EcPath.x_compare x1 x2
  | _, _ -> Stdlib.compare (pv_kind v1) (pv_kind v2)

let pv_compare_p v1 v2 =
  match v1, v2 with
  | PVloc i1,  PVloc i2  -> EcSymbols.sym_compare i1 i2
  | PVglob x1, PVglob x2 -> EcPath.x_compare_na x1 x2
  | _, _ -> Stdlib.compare (pv_kind v1) (pv_kind v2)

let pv_ntr_compare v1 v2 =
  match v1, v2 with
  | PVloc i1,  PVloc i2  -> EcSymbols.sym_compare i1 i2
  | PVglob x1, PVglob x2 -> EcPath.x_ntr_compare x1 x2
  | _, _ -> Stdlib.compare (pv_kind v1) (pv_kind v2)

let is_loc  = function PVloc _ -> true  | PVglob _ -> false
let is_glob = function PVloc _ -> false | PVglob _ -> true

let get_loc = function PVloc id -> id | PVglob _ -> assert false
let get_glob = function PVloc _ -> assert false | PVglob xp -> xp

let symbol_of_pv = function
  | PVglob x -> x.EcPath.x_sub
  | PVloc id -> id

let string_of_pvar_kind = function
  | PVKglob -> "PVKglob"
  | PVKloc  -> "PVKloc"

let string_of_pvar (p : prog_var) =
  let sp = match p with
    | PVglob x -> EcPath.x_tostring x
    | PVloc id -> id in

  Printf.sprintf "%s[%s]"
    sp (string_of_pvar_kind (pv_kind p))

let name_of_pvar pv =
  match pv with
  | PVloc x -> x
  | PVglob xp -> EcPath.xbasename xp

let pv_loc id = PVloc id

let arg_symbol = "arg"
let res_symbol = "res"
let pv_arg = PVloc arg_symbol
let pv_res =  PVloc res_symbol

let xp_glob x =
  let top = x.EcPath.x_top in
  if top.EcPath.m_args = [] then x else
    (* remove the functor argument *)
    let ntop = EcPath.mpath top.m_top [] in
    EcPath.xpath ntop x.EcPath.x_sub

let pv_glob x = PVglob (xp_glob x)

let pv_subst m_subst px = match px with
  | PVglob x ->
    let mp' = m_subst x in
    if x == mp' then px else pv_glob mp'
  | PVloc _ -> px

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

let pv_fv = function
  | PVglob x -> EcPath.x_fv Mid.empty x
  | PVloc _ -> Mid.empty

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

let e_proj_simpl e i ty =
  match e.e_node with
  | Etuple es -> List.nth es i
  | _ -> e_proj e i ty

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

let e_app_op ?(tyargs=[]) op args ty =
  e_app (e_op op tyargs (toarrow (List.map e_ty args) ty)) args ty

(* -------------------------------------------------------------------- *)
module Reals : sig
  val of_lit : EcBigInt.zint -> expr
  val of_int : expr -> expr
  val add    : expr -> expr -> expr
  val opp    : expr -> expr
  val sub    : expr -> expr -> expr
  val mul    : expr -> expr -> expr
  val inv    : expr -> expr
  val div    : expr -> expr -> expr
end = struct
  module CIR = EcCoreLib.CI_Real

  let of_int f = e_app_op CIR.p_real_of_int [f] treal
  let of_lit n = of_int (e_int n)

  let add f1 f2 = e_app_op CIR.p_real_add [f1; f2] treal
  let opp f     = e_app_op CIR.p_real_opp [f] treal
  let sub f1 f2 = add f1 (opp f2)
  let mul f1 f2 = e_app_op CIR.p_real_mul [f1; f2] treal
  let inv f     = e_app_op CIR.p_real_inv [f] treal
  let div f1 f2 = mul f1 (inv f2)
end

(* -------------------------------------------------------------------- *)
let e_decimal (n, (l, f)) =
  if EcBigInt.equal f EcBigInt.zero then Reals.of_lit n else

  let d   = EcBigInt.pow (EcBigInt.of_int 10) l in
  let gcd = EcBigInt.gcd f d in
  let f   = EcBigInt.div f gcd in
  let d   = EcBigInt.div d gcd in
  let fct = Reals.div (Reals.of_lit f) (Reals.of_lit d) in

  if   EcBigInt.equal n EcBigInt.zero
  then fct
  else Reals.add (Reals.of_lit n) fct

(* -------------------------------------------------------------------- *)
let e_none (ty : ty) : expr =
  e_op EcCoreLib.CI_Option.p_none [ty] (toption ty)

let e_some ({ e_ty = ty } as e : expr) : expr =
  let op = e_op EcCoreLib.CI_Option.p_some [ty] (tfun ty (toption ty)) in
  e_app op [e] (toption ty)

let e_oget (e : expr) (ty : ty) : expr =
  let op = e_op EcCoreLib.CI_Option.p_oget [ty] (tfun (toption ty) ty) in
  e_app op [e] ty

(* -------------------------------------------------------------------- *)
let e_map fty fe e =
  match e.e_node with
  | Eint _ | Elocal _ | Evar _ -> e

  | Eop (p, tys) ->
      let tys' = List.Smart.map fty tys in
      let ty'  = fty e.e_ty in
        e_op p tys' ty'

  | Eapp (e1, args) ->
      let e1'   = fe e1 in
      let args' = List.Smart.map fe args in
      let ty'   = fty e.e_ty in
        e_app e1' args' ty'

  | Elet (lp, e1, e2) ->
      let e1' = fe e1 in
      let e2' = fe e2 in
        e_let lp e1' e2'

  | Etuple le ->
      let le' = List.Smart.map fe le in
        e_tuple le'

  | Eproj (e1, i) ->
      let e' = fe e1 in
      let ty = fty e.e_ty in
      e_proj e' i ty

  | Eif (e1, e2, e3) ->
      let e1' = fe e1 in
      let e2' = fe e2 in
      let e3' = fe e3 in
      e_if e1' e2' e3'

  | Ematch (b, es, ty) ->
      let ty' = fty ty in
      let b'  = fe b in
      let es' = List.Smart.map fe es in
      e_match b' es' ty'

  | Equant (q, b, bd) ->
      let dop (x, ty as xty) =
        let ty' = fty ty in
          if ty == ty' then xty else (x, ty') in
      let b'  = List.Smart.map dop b in
      let bd' = fe bd in
      e_quantif q b' bd'

let e_fold (fe : 'a -> expr -> 'a) (state : 'a) (e : expr) =
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

let e_iter (fe : expr -> unit) (e : expr) =
  e_fold (fun () e -> fe e) () e

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
    es_mp      : smsubst;
    es_loc     : expr Mid.t;
}

let e_subst_id = {
    es_freshen = false;
    es_p       = identity;
    es_ty      = identity;
    es_opdef   = Mp.empty;
    es_mp      = sms_identity;
    es_loc     = Mid.empty;
}

(* -------------------------------------------------------------------- *)
let is_e_subst_id s =
     not s.es_freshen
  && s.es_p  == identity
  && s.es_ty == identity
  && Mp.is_empty s.es_opdef
  && sms_is_identity s.es_mp
  && Mid.is_empty s.es_loc

(* -------------------------------------------------------------------- *)
let e_subst_init freshen on_path on_ty opdef on_mpath esloc =
  { es_freshen = freshen;
    es_p       = on_path;
    es_ty      = on_ty;
    es_opdef   = opdef;
    es_mp      = on_mpath;
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
        (s, LSymbol x')

  | LTuple xs ->
      let (s, xs') = add_locals s xs in
        (s, LTuple xs')

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
        (s, LRecord (s.es_p p, xs'))

(* -------------------------------------------------------------------- *)
let rec e_subst (s: e_subst) e =
  match e.e_node with
  | Elocal id -> begin
      match Mid.find_opt id s.es_loc with
      | Some e' -> e'
      | None    ->
(* FIXME schema *)
(*        assert (not s.es_freshen); *)
        e_local id (s.es_ty e.e_ty)
  end

  | Evar pv ->
      let pv' = pv_subst (x_subst s.es_mp) pv in
      let ty' = s.es_ty e.e_ty in
        e_var pv' ty'

  | Eapp ({ e_node = Eop (p, tys) }, args) when Mp.mem p s.es_opdef ->
      let tys  = List.Smart.map s.es_ty tys in
      let ty   = s.es_ty e.e_ty in
      let body = oget (Mp.find_opt p s.es_opdef) in
        e_subst_op ~freshen:s.es_freshen ty tys (List.map (e_subst s) args) body

  | Eop (p, tys) when Mp.mem p s.es_opdef ->
      let tys  = List.Smart.map s.es_ty tys in
      let ty   = s.es_ty e.e_ty in
      let body = oget (Mp.find_opt p s.es_opdef) in
        e_subst_op ~freshen:s.es_freshen ty tys [] body

  | Eop (p, tys) ->
      let p'   = s.es_p p in
      let tys' = List.Smart.map s.es_ty tys in
      let ty'  = s.es_ty e.e_ty in
        e_op p' tys' ty'

  | Elet (lp, e1, e2) ->
      let e1' = e_subst s e1 in
      let s, lp' = subst_lpattern s lp in
      let e2' = e_subst s e2 in
        e_let lp' e1' e2'

  | Equant (q, b, e1) ->
      let s, b' = add_locals s b in
      let e1' = e_subst s e1 in
        e_quantif q b' e1'

  | _ -> e_map s.es_ty (e_subst s) e

and e_subst_op ~freshen ety tys args (tyids, e) =
  (* FIXME: factor this out *)
  (* FIXME: is es_freshen value correct? *)

  let e =
    let sty = Tvar.init tyids tys in
    let sty = ty_subst { ty_subst_id with ts_v = Mid.find_opt^~ sty; } in
    let sty = { e_subst_id with
                  es_freshen = freshen;
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

(* -------------------------------------------------------------------- *)
let destr_app = function
    { e_node = Eapp (e, es) } -> (e, es) | e -> (e, [])

(* -------------------------------------------------------------------- *)
let split_args e =
  match e.e_node with
  | Eapp (e, args) -> (e, args)
  | _ -> (e, [])
