(* -------------------------------------------------------------------- *)
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
 
let toarrow dom ty = 
  List.fold_right tfun dom ty

(* -------------------------------------------------------------------- *)
let map f t = 
  match t.ty_node with 
  | Tunivar _ | Tvar _ -> t
  | Ttuple lty -> ttuple (List.map f lty)
  | Tconstr(p, lty) -> tconstr p (List.map f lty)
  | Tfun(t1,t2)     -> tfun (f t1) (f t2)

let fold f s ty = 
  match ty.ty_node with 
  | Tunivar _ | Tvar _ -> s
  | Ttuple lty -> List.fold_left f s lty
  | Tconstr(_, lty) -> List.fold_left f s lty
  | Tfun(t1,t2) -> f (f s t1) t2

let sub_exists f t =
  match t.ty_node with
  | Tunivar _ | Tvar _ -> false
  | Ttuple lty -> List.exists f lty
  | Tconstr (_, lty) -> List.exists f lty
  | Tfun (t1,t2) -> f t1 || f t2
  
(* -------------------------------------------------------------------- *)
module Tuni = struct
  let subst1 ((id, t) : uid * ty) =
    let rec aux ty = 
      match ty.ty_node with 
      | Tunivar id' when uid_equal id id' -> t
      | _ -> map aux ty in
    aux

  let subst (uidmap : ty Muid.t) =
    let rec aux ty = 
      match ty.ty_node with 
      | Tunivar id -> odfl ty (Muid.find_opt id uidmap)
      | _ -> map aux ty in
    aux 

  let subst_dom uidmap = List.map (subst uidmap)

  let occur u = 
    let rec aux t = 
      match t.ty_node with
      | Tunivar u' -> uid_equal u u'
      | _ -> sub_exists aux t in
    aux

  let rec fv_rec fv t = 
    match t.ty_node with
    | Tunivar id -> Suid.add id fv 
    | _ -> fold fv_rec fv t 

  let fv = fv_rec Suid.empty

  let fv_sig (dom, codom) = 
    List.fold_left fv_rec (fv codom) dom
end

module Tvar = struct 
  let subst1 (id,t) = 
    let rec aux ty = 
      match ty.ty_node with 
      | Tvar id' when id_equal id id' -> t
      | _ -> map aux ty in
    aux

  let subst (s : ty Mid.t) =
    let rec aux t = 
      match t.ty_node with 
      | Tvar id -> odfl t (Mid.find_opt id s)
      | _ -> map aux t in
    aux 

  let init lv lt = 
    assert (List.length lv = List.length lt);
    List.fold_left2 (fun s v t -> Mid.add v t s) Mid.empty lv lt

  let rec fv_rec fv t = 
    match t.ty_node with
    | Tvar id -> Sid.add id fv 
    | _ -> fold fv_rec fv t 

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

(* -------------------------------------------------------------------- *)
type lpattern =
  | LSymbol of EcIdent.t
  | LTuple  of EcIdent.t list

let lp_equal p1 p2 = 
  match p1, p2 with
  | LSymbol x1, LSymbol x2 -> EcIdent.id_equal x1 x2
  | LTuple lx1, LTuple lx2 -> List.all2 EcIdent.id_equal lx1 lx2
  | _ -> false

let lp_hash = function
  | LSymbol x -> EcIdent.tag x
  | LTuple lx -> Why3.Hashcons.combine_list EcIdent.tag 0 lx

(* -------------------------------------------------------------------- *)
type tyexpr = {
  tye_node : tyexpr_node;
  tye_tag  : int;
}

and tyexpr_node =
  | Eint   of int                        (* int. literal          *)
  | Elocal of EcIdent.t                  (* let-variables         *)
  | Evar   of prog_var                   (* module variable       *)
  | Eop    of EcPath.path * ty list      (* op apply to type args *)
  | Eapp   of tyexpr * tyexpr list       (* op. application       *)
  | Elet   of lpattern * tyexpr * tyexpr (* let binding           *)
  | Etuple of tyexpr list                (* tuple constructor     *)
  | Eif    of tyexpr * tyexpr * tyexpr   (* _ ? _ : _             *)

(* -------------------------------------------------------------------- *)
let e_equal   = ((==) : tyexpr -> tyexpr -> bool)
let e_hash    = fun e -> e.tye_tag
let e_compare = fun e1 e2 -> e_hash e1 - e_hash e2

(* -------------------------------------------------------------------- *)
module Hexpr = Why3.Hashcons.Make (struct 
  type t = tyexpr

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

  let equal e1 e2 = equal_node e1.tye_node e2.tye_node

  let hash e = 
    match e.tye_node with
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
          
  let tag n e = { e with tye_tag = n }
end)

(* -------------------------------------------------------------------- *)
let mk_tyexpr e =
  Hexpr.hashcons { tye_node = e; tye_tag = -1; }

let e_int   = fun i        -> mk_tyexpr (Eint i)
let e_local = fun x        -> mk_tyexpr (Elocal x)
let e_var   = fun x        -> mk_tyexpr (Evar x)
let e_op    = fun x targs  -> mk_tyexpr (Eop (x, targs))
let e_let   = fun pt e1 e2 -> mk_tyexpr (Elet (pt, e1, e2))
let e_tuple = fun es       -> mk_tyexpr (Etuple es)
let e_if    = fun c e1 e2  -> mk_tyexpr (Eif (c, e1, e2))

let e_app x args = 
  match x.tye_node with
  | Eapp(x', args') -> mk_tyexpr (Eapp (x', (args'@args)))
  | _ -> mk_tyexpr (Eapp (x, args))

(* -------------------------------------------------------------------- *)
let ids_of_lpattern = function
  | LSymbol id -> [id] 
  | LTuple ids -> ids

let e_map fty fe e =
  match e.tye_node with 
  | Eint _
  | Elocal _
  | Evar _                -> e
  | Eop (p, tys)          -> e_op p (List.map fty tys)
  | Eapp (e, args)        -> e_app (fe e) (List.map fe args)
  | Elet (lp, e1, e2)     -> e_let lp (fe e1) (fe e2)
  | Etuple le             -> e_tuple (List.map fe le)
  | Eif (e1, e2, e3)      -> e_if (fe e1) (fe e2) (fe e3)

let rec e_fold fe state e =
  e_fold_r fe state e.tye_node

and e_fold_r fe state e =
  match e with
  | Eint _                -> state
  | Elocal _              -> state
  | Evar _                -> state
  | Eop _                 -> state
  | Eapp (e, args)        -> List.fold_left fe (fe state e) args
  | Elet (_, e1, e2)      -> List.fold_left fe state [e1; e2]
  | Etuple es             -> List.fold_left fe state es
  | Eif (e1, e2, e3)      -> List.fold_left fe state [e1; e2; e3]


(* -------------------------------------------------------------------- *)
module Esubst = struct 
  let mapty onty = 
    let rec aux e = e_map onty aux e in
      aux 

  let uni (uidmap : ty Muid.t) = mapty (Tuni.subst uidmap)
end

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
      match e.tye_node with
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
