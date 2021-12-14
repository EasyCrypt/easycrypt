(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcTypes
open EcPath

module Sid = EcIdent.Sid
module Mid = EcIdent.Mid

(* -------------------------------------------------------------------- *)
type lvalue =
  | LvVar   of (EcTypes.prog_var * EcTypes.ty)
  | LvTuple of (EcTypes.prog_var * EcTypes.ty) list

let lv_equal lv1 lv2 =
  match lv1, lv2 with
  | LvVar (pv1, ty1), LvVar (pv2, ty2) ->
         (EcTypes.pv_equal pv1 pv2)
      && (EcTypes.ty_equal ty1 ty2)

  | LvTuple tu1, LvTuple tu2 ->
      List.all2
        (fun (pv1, ty1) (pv2, ty2) ->
             (EcTypes.pv_equal pv1 pv2)
          && (EcTypes.ty_equal ty1 ty2))
        tu1 tu2

  | _, _ -> false

(* -------------------------------------------------------------------- *)
let lv_fv = function
  | LvVar (pv, _) ->
      EcTypes.pv_fv pv

  | LvTuple pvs ->
      let add s (pv, _) = EcIdent.fv_union s (EcTypes.pv_fv pv) in
      List.fold_left add Mid.empty pvs

let symbol_of_lv = function
  | LvVar (pv, _) ->
      EcTypes.symbol_of_pv pv

  | LvTuple pvs ->
      String.concat "" (List.map (EcTypes.symbol_of_pv |- fst) pvs)

let ty_of_lv = function
  | LvVar   (_, ty)       -> ty
  | LvTuple tys           -> EcTypes.ttuple (List.map snd tys)

let lv_of_list = function
  | [] -> None
  | [(pv, ty)] -> Some (LvVar (pv, ty))
  | pvs -> Some (LvTuple pvs)

(* -------------------------------------------------------------------- *)
type instr = {
  i_node : instr_node;
  i_fv : int Mid.t;
  i_tag  : int;
}

and instr_node =
  | Sasgn     of lvalue * EcTypes.expr
  | Srnd      of lvalue * EcTypes.expr
  | Scall     of lvalue option * EcPath.xpath * EcTypes.expr list
  | Sif       of EcTypes.expr * stmt * stmt
  | Swhile    of EcTypes.expr * stmt
  | Smatch    of expr * ((EcIdent.t * EcTypes.ty) list * stmt) list
  | Sassert   of EcTypes.expr
  | Sabstract of EcIdent.t

and stmt = {
  s_node : instr list;
  s_fv   : int Mid.t;
  s_tag  : int;
}

(* -------------------------------------------------------------------- *)
let i_equal   = ((==) : instr -> instr -> bool)
let i_hash    = fun i -> i.i_tag
let i_compare = fun i1 i2 -> i_hash i1 - i_hash i2
let i_fv i    = i.i_fv
let i_node i  = i.i_node

let s_equal   = ((==) : stmt -> stmt -> bool)
let s_hash    = fun s -> s.s_tag
let s_compare = fun s1 s2 -> s_hash s1 - s_hash s2
let s_fv      = fun s -> s.s_fv

(* -------------------------------------------------------------------- *)
module Hinstr = Why3.Hashcons.Make (struct
  type t = instr

  let equal_node i1 i2 =
    match i1, i2 with
    | Sasgn (lv1, e1), Sasgn (lv2, e2) ->
        (lv_equal lv1 lv2) && (EcTypes.e_equal e1 e2)

    | Srnd (lv1, e1), Srnd (lv2, e2) ->
        (lv_equal lv1 lv2) && (EcTypes.e_equal e1 e2)

    | Scall (lv1, f1, es1), Scall (lv2, f2, es2) ->
           (EcUtils.opt_equal lv_equal lv1 lv2)
        && (EcPath.x_equal f1 f2)
        && (List.all2 EcTypes.e_equal es1 es2)

    | Sif (c1, s1, r1), Sif (c2, s2, r2) ->
           (EcTypes.e_equal c1 c2)
        && (s_equal s1 s2)
        && (s_equal r1 r2)

    | Swhile (c1, s1), Swhile (c2, s2) ->
           (EcTypes.e_equal c1 c2)
        && (s_equal s1 s2)

    | Smatch (e1, b1), Smatch (e2, b2) when List.length b1 = List.length b2 ->
        let forb (bs1, s1) (bs2, s2) =
          let forbs (x1, ty1) (x2, ty2) =
               EcIdent.id_equal x1  x2
            && EcTypes.ty_equal ty1 ty2
          in List.all2 forbs bs1 bs2 && s_equal s1 s2
        in EcTypes.e_equal e1 e2 && List.all2 forb b1 b2

    | Sassert e1, Sassert e2 ->
        (EcTypes.e_equal e1 e2)

    | Sabstract id1, Sabstract id2 -> EcIdent.id_equal id1 id2

    | _, _ -> false

  let equal i1 i2 = equal_node i1.i_node i2.i_node

  let hash p =
    match p.i_node with
    | Sasgn (lv, e) ->
        Why3.Hashcons.combine
          (Hashtbl.hash lv) (EcTypes.e_hash e)

    | Srnd (lv, e) ->
        Why3.Hashcons.combine
          (Hashtbl.hash lv) (EcTypes.e_hash e)

    | Scall (lv, f, tys) ->
        Why3.Hashcons.combine_list EcTypes.e_hash
          (Why3.Hashcons.combine
             (Hashtbl.hash lv) (EcPath.x_hash f))
          tys

    | Sif (c, s1, s2) ->
        Why3.Hashcons.combine2
          (EcTypes.e_hash c) (s_hash s1) (s_hash s2)

    | Swhile (c, s) ->
        Why3.Hashcons.combine (EcTypes.e_hash c) (s_hash s)

    | Smatch (e, b) ->
        let forb (bds, s) =
          let forbs (x, ty) =
            Why3.Hashcons.combine (EcIdent.id_hash x) (EcTypes.ty_hash ty)
          in Why3.Hashcons.combine_list forbs (s_hash s) bds
        in Why3.Hashcons.combine_list forb (EcTypes.e_hash e) b

    | Sassert e -> EcTypes.e_hash e

    | Sabstract id -> EcIdent.id_hash id

  let i_fv   = function
    | Sasgn (lv, e) ->
        EcIdent.fv_union (lv_fv lv) (EcTypes.e_fv e)

    | Srnd (lv, e) ->
        EcIdent.fv_union (lv_fv lv) (EcTypes.e_fv e)

    | Scall (olv, f, args) ->
        let ffv = EcPath.x_fv Mid.empty f in
        let ofv = olv |> omap lv_fv |> odfl Mid.empty in
        List.fold_left
          (fun s a -> EcIdent.fv_union s (EcTypes.e_fv a))
          (EcIdent.fv_union ffv ofv) args

    | Sif (e, s1, s2) ->
        List.fold_left EcIdent.fv_union Mid.empty
          [EcTypes.e_fv e; s_fv s1; s_fv s2]

    | Swhile (e, s)  ->
        EcIdent.fv_union (EcTypes.e_fv e) (s_fv s)

    | Smatch (e, b) ->
        let forb (bs, s) =
          let bs = Sid.of_list (List.map fst bs) in
          EcIdent.fv_diff (s_fv s) bs

        in List.fold_left
             (fun s b -> EcIdent.fv_union s (forb b))
             (EcTypes.e_fv e) b

    | Sassert e    ->
        EcTypes.e_fv e

    | Sabstract id ->
        EcIdent.fv_singleton id

  let tag n p = { p with i_tag = n; i_fv = i_fv p.i_node }
end)

(* -------------------------------------------------------------------- *)
module Hstmt = Why3.Hashcons.Make (struct
  type t = stmt

  let equal_node s1 s2 =
    List.all2 i_equal s1 s2

  let equal s1 s2 = equal_node s1.s_node s2.s_node

  let hash p =
    Why3.Hashcons.combine_list i_hash 0 p.s_node

  let tag n p =
    let fv =
      List.fold_left
        (fun s i -> EcIdent.fv_union s (i_fv i))
        Mid.empty p.s_node
    in { p with s_tag = n; s_fv = fv; }
end)

(* -------------------------------------------------------------------- *)
module MSHi = EcMaps.MakeMSH(struct type t = instr let tag i = i.i_tag end)
module Si   = MSHi.S
module Mi   = MSHi.M
module Hi   = MSHi.H

(* -------------------------------------------------------------------- *)
let mk_instr i = Hinstr.hashcons
  { i_node = i; i_tag = -1; i_fv = Mid.empty }

let stmt s = Hstmt.hashcons
  { s_node = s; s_tag = -1; s_fv = Mid.empty}

let rstmt s = stmt (List.rev s)

(* --------------------------------------------------------------------- *)
let i_asgn     (lv, e)      = mk_instr (Sasgn (lv, e))
let i_rnd      (lv, e)      = mk_instr (Srnd (lv, e))
let i_call     (lv, m, tys) = mk_instr (Scall (lv, m, tys))
let i_if       (c, s1, s2)  = mk_instr (Sif (c, s1, s2))
let i_while    (c, s)       = mk_instr (Swhile (c, s))
let i_match    (e, b)       = mk_instr (Smatch (e, b))
let i_assert   e            = mk_instr (Sassert e)
let i_abstract id           = mk_instr (Sabstract id)

let s_seq      s1 s2        = stmt (s1.s_node @ s2.s_node)
let s_empty                 = stmt []

let s_asgn     arg = stmt [i_asgn arg]
let s_rnd      arg = stmt [i_rnd arg]
let s_call     arg = stmt [i_call arg]
let s_if       arg = stmt [i_if arg]
let s_while    arg = stmt [i_while arg]
let s_match    arg = stmt [i_match arg]
let s_assert   arg = stmt [i_assert arg]
let s_abstract arg = stmt [i_abstract arg]

(* -------------------------------------------------------------------- *)
let get_asgn = function
  | { i_node = Sasgn (lv, e) } -> Some (lv, e)
  | _ -> None

let get_rnd = function
  | { i_node = Srnd (lv, e) } -> Some (lv, e)
  | _ -> None

let get_call = function
  | { i_node = Scall (lv, f, fs) } -> Some (lv, f, fs)
  | _ -> None

let get_if = function
  | { i_node = Sif (e, s1, s2) } -> Some (e, s1, s2)
  | _ -> None

let get_while = function
  | { i_node = Swhile (e, s) } -> Some (e, s)
  | _ -> None

let get_match = function
  | { i_node = Smatch (e, b) } -> Some (e, b)
  | _ -> None

let get_assert = function
  | { i_node = Sassert e } -> Some e
  | _ -> raise Not_found

(* -------------------------------------------------------------------- *)
let _destr_of_get (get : instr -> 'a option) (i : instr) =
  match get i with Some x -> x | None -> raise Not_found

let destr_asgn   = _destr_of_get get_asgn
let destr_rnd    = _destr_of_get get_rnd
let destr_call   = _destr_of_get get_call
let destr_if     = _destr_of_get get_if
let destr_while  = _destr_of_get get_while
let destr_match  = _destr_of_get get_match
let destr_assert = _destr_of_get get_assert

(* -------------------------------------------------------------------- *)
let _is_of_get (get : instr -> 'a option) (i : instr) =
  EcUtils.is_some (get i)

let is_asgn   = _is_of_get get_asgn
let is_rnd    = _is_of_get get_rnd
let is_call   = _is_of_get get_call
let is_if     = _is_of_get get_if
let is_while  = _is_of_get get_while
let is_match  = _is_of_get get_match
let is_assert = _is_of_get get_assert

(* -------------------------------------------------------------------- *)
module ISmart : sig
  type lv_var   = EcTypes.prog_var * EcTypes.ty
  type lv_tuple = lv_var list

  val lv_var   : lvalue * lv_var   -> lv_var   -> lvalue
  val lv_tuple : lvalue * lv_tuple -> lv_tuple -> lvalue

  type i_asgn     = lvalue * EcTypes.expr
  type i_rnd      = lvalue * EcTypes.expr
  type i_call     = lvalue option * EcPath.xpath * EcTypes.expr list
  type i_if       = EcTypes.expr * stmt * stmt
  type i_while    = EcTypes.expr * stmt
  type i_match    = EcTypes.expr * ((EcIdent.t * ty) list * stmt) list
  type i_assert   = EcTypes.expr
  type i_abstract = EcIdent.t

  val i_asgn     : (instr * i_asgn    ) -> i_asgn     -> instr
  val i_rnd      : (instr * i_rnd     ) -> i_rnd      -> instr
  val i_call     : (instr * i_call    ) -> i_call     -> instr
  val i_if       : (instr * i_if      ) -> i_if       -> instr
  val i_while    : (instr * i_while   ) -> i_while    -> instr
  val i_match    : (instr * i_match   ) -> i_match    -> instr
  val i_assert   : (instr * i_assert  ) -> i_assert   -> instr
  val i_abstract : (instr * i_abstract) -> i_abstract -> instr

  val s_stmt : stmt -> instr list -> stmt
end = struct
  type lv_var   = EcTypes.prog_var * EcTypes.ty
  type lv_tuple = lv_var list

  type i_asgn     = lvalue * EcTypes.expr
  type i_rnd      = lvalue * EcTypes.expr
  type i_call     = lvalue option * EcPath.xpath * EcTypes.expr list
  type i_if       = EcTypes.expr * stmt * stmt
  type i_while    = EcTypes.expr * stmt
  type i_match    = EcTypes.expr * ((EcIdent.t * ty) list * stmt) list
  type i_assert   = EcTypes.expr
  type i_abstract = EcIdent.t

  let lv_var (lv, pvt) pvt' =
    if pvt == pvt' then lv else LvVar pvt'

  let lv_tuple (lv, pvs) pvs' =
    if pvs == pvs' then lv else LvTuple pvs'

  let i_asgn (i, (lv, e)) (lv', e') =
    if lv == lv' && e == e' then i else i_asgn (lv', e')

  let i_rnd (i, (lv, e)) (lv', e') =
    if lv == lv' && e == e' then i else i_rnd (lv', e')

  let i_call (i, (olv, mp, args)) (olv', mp', args') =
    if   olv == olv' && mp == mp' && args == args'
    then i else  i_call (olv', mp', args')

  let i_if (i, (e, s1, s2)) (e', s1', s2') =
    if   e == e' && s1 == s1' && s2 == s2'
    then i else i_if (e', s1', s2')

  let i_while (i, (e, s)) (e', s') =
    if e == e' && s == s' then i else i_while (e', s')

  let i_match (i, (e, b)) (e', b') =
    if e == e' && b == b' then i else i_match (e', b')

  let i_assert (i, e) e' =
    if e == e' then i else i_assert e'

  let i_abstract (i, x) x' =
    if x == x' then i else i_abstract x

  let s_stmt s is' =
    if s.s_node == is' then s else stmt is'
end

(* -------------------------------------------------------------------- *)
let rec s_subst_top (s : EcTypes.e_subst) =
  let e_subst = EcTypes.e_subst s in

  if e_subst == identity then identity else

  let pvt_subst (pv,ty as p) =
    let pv' = EcTypes.pv_subst s.EcTypes.es_xp pv in
    let ty' = s.EcTypes.es_ty ty in

    if pv == pv' && ty == ty' then p else (pv', ty') in

  let lv_subst lv =
    match lv with
    | LvVar pvt ->
        ISmart.lv_var (lv, pvt) (pvt_subst pvt)

    | LvTuple pvs ->
        let pvs' = List.Smart.map pvt_subst pvs in
        ISmart.lv_tuple (lv, pvs) pvs'

  in

  let rec i_subst i =
    match i.i_node with
    | Sasgn (lv, e) ->
        ISmart.i_asgn (i, (lv, e)) (lv_subst lv, e_subst e)

    | Srnd (lv, e) ->
        ISmart.i_rnd (i, (lv, e)) (lv_subst lv, e_subst e)

    | Scall (olv, mp, args) ->
        let olv'  = olv |> OSmart.omap lv_subst in
        let mp'   = s.EcTypes.es_xp mp in
        let args' = List.Smart.map e_subst args in

        ISmart.i_call (i, (olv, mp, args)) (olv', mp', args')

    | Sif (e, s1, s2) ->
        ISmart.i_if (i, (e, s1, s2))
          (e_subst e, s_subst s1, s_subst s2)

    | Swhile(e, b) ->
        ISmart.i_while (i, (e, b)) (e_subst e, s_subst b)

    | Smatch (e, b) ->
        let forb ((xs, subs) as b1) =
          let s, xs' = EcTypes.add_locals s xs in
          let subs'  = s_subst_top s subs in
          if xs == xs' && subs == subs' then b1 else (xs', subs')
        in

        ISmart.i_match (i, (e, b)) (e_subst e, List.Smart.map forb b)

    | Sassert e ->
        ISmart.i_assert (i, e) (e_subst e)

    | Sabstract _ ->
        i

  and s_subst s =
    ISmart.s_stmt s (List.Smart.map i_subst s.s_node)

  in s_subst

let s_subst = s_subst_top

(* -------------------------------------------------------------------- *)
module Uninit = struct    (* FIXME: generalize this for use in ecPV *)
  let e_pv e =
    let rec e_pv sid e =
      match e.e_node with
      | Evar (PVglob _) -> sid
      | Evar (PVloc id) -> Ssym.add id sid
      | _               -> e_fold e_pv sid e in

    e_pv Ssym.empty e
end

let rec lv_get_uninit_read (w : Ssym.t) (lv : lvalue) =
  let sx_of_pv pv = match pv with
    | PVloc v -> Ssym.singleton v
    | PVglob _ -> Ssym.empty
  in

  match lv with
  | LvVar (x, _) ->
      Ssym.union (sx_of_pv x) w

  | LvTuple xs ->
      let w' = List.map (sx_of_pv |- fst) xs in
      Ssym.big_union (w :: w')

and s_get_uninit_read (w : Ssym.t) (s : stmt) =
  let do1 (w, r) i =
    let w, r' = i_get_uninit_read w i in
    (w, Ssym.union r r')

  in List.fold_left do1 (w, Ssym.empty) s.s_node

and i_get_uninit_read (w : Ssym.t) (i : instr) =
  match i.i_node with
  | Sasgn (lv, e) | Srnd (lv, e) ->
      let r1 = Ssym.diff (Uninit.e_pv e) w in
      let w2 = lv_get_uninit_read w lv in
      (Ssym.union w w2, r1)

  | Scall (olv, _, args) ->
      let r1 = Ssym.diff (Ssym.big_union (List.map (Uninit.e_pv) args)) w in
      let w = olv |> omap (lv_get_uninit_read w) |> odfl w in
      (w, r1)

  | Sif (e, s1, s2) ->
      let r = Ssym.diff (Uninit.e_pv e) w in
      let w1, r1 = s_get_uninit_read w s1 in
      let w2, r2 = s_get_uninit_read w s2 in
      (Ssym.union w (Ssym.inter w1 w2), Ssym.big_union [r; r1; r2])

  | Swhile (e, s) ->
      let r  = Ssym.diff (Uninit.e_pv e) w in
      let rs = snd (s_get_uninit_read w s) in
      (w, Ssym.union r rs)

  | Smatch (e, bs) ->
      let r   = Ssym.diff (Uninit.e_pv e) w in
      let wrs = List.map (fun (_, b) -> s_get_uninit_read w b) bs in
      let ws, rs = List.split wrs in
      (Ssym.union w (Ssym.big_inter ws), Ssym.big_union (r :: rs))

  | Sassert e ->
      (w, Ssym.diff (Uninit.e_pv e) w)

  | Sabstract (_ : EcIdent.t) ->
      (w, Ssym.empty)

let get_uninit_read (s : stmt) =
  snd (s_get_uninit_read Ssym.empty s)

(* -------------------------------------------------------------------- *)
type 'a use_restr = {
  ur_pos : 'a option;   (* If not None, can use only element in this set. *)
  ur_neg : 'a;          (* Cannot use element in this set. *)
}

let ur_app f a =
  { ur_pos = (omap f) a.ur_pos;
    ur_neg = f a.ur_neg; }

(* Noting is restricted. *)
let ur_empty emp = { ur_pos = None; ur_neg = emp; }

(* Everything is restricted. *)
let ur_full emp = { ur_pos = Some emp; ur_neg = emp; }

let ur_pos_subset subset ur1 ur2 = match ur1,ur2 with
  | _, None -> true             (* Indeed, [None] means everybody. *)
  | None, Some _ -> false
  | Some s1, Some s2 -> subset s1 s2

let ur_equal (equal : 'a -> 'a -> bool) ur1 ur2 =
  equal ur1.ur_neg ur2.ur_neg
  && (opt_equal equal) ur1.ur_pos ur2.ur_pos

(* Union for negative restrictions, intersection for positive ones.
   [None] stands for everybody. *)
let ur_union union inter ur1 ur2 =
  let ur_pos = match ur1.ur_pos, ur2.ur_pos with
    | None, None -> None
    | None, Some s | Some s, None -> Some s
    | Some s1, Some s2 -> some @@ inter s1 s2 in

  { ur_pos = ur_pos;
    ur_neg = union ur1.ur_neg ur2.ur_neg; }

(* Converse of ur_union. *)
let ur_inter union inter ur1 ur2 =
  let ur_pos = match ur1.ur_pos, ur2.ur_pos with
    | None, _ | _, None -> None
    | Some s1, Some s2 -> some @@ union s1 s2 in

  { ur_pos = ur_pos;
    ur_neg = inter ur1.ur_neg ur2.ur_neg; }

(* -------------------------------------------------------------------- *)
(* Oracle information of a procedure [M.f]. *)
module PreOI : sig
  type 'a t

  val hash : ('a -> int) -> 'a t -> int
  val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool

  val is_in : 'a t -> bool

  val cost_self : 'a t -> [`Bounded of 'a | `Unbounded]
  val cost : 'a t -> xpath -> [`Bounded of 'a | `Zero | `Unbounded]
  val cost_calls : 'a t -> [`Bounded of 'a Mx.t | `Unbounded]
  val costs : 'a t -> [`Bounded of 'a * 'a Mx.t | `Unbounded]

  val allowed : 'a t -> xpath list
  val allowed_s : 'a t -> Sx.t

  val mk : xpath list -> bool -> [`Bounded of 'a * 'a Mx.t | `Unbounded] -> 'a t
  (* val change_calls : 'a t -> xpath list -> 'a t *)
  val filter : (xpath -> bool) -> 'a t -> 'a t
end = struct
  (* Oracle information of a procedure [M.f]:
   * - oi_calls : list of oracles that can be called by [M.f].
   * - oi_in    : true if equality of globals is required to ensure
   * equality of result and globals (in the post).
   * - oi_costs : self cost, plus a mapping from oracles to the number of time
   * that they can be called by [M.f]. Missing entries are can be called
   * zero times. No restrictio of [None]
   *
   * Remark: there is redundancy between oi_calls and oi_costs. *)
  type 'a t = {
    oi_calls : xpath list;
    oi_in    : bool;
    oi_costs : ('a * 'a Mx.t) option;
  }

  let is_in t = t.oi_in

  let allowed oi = oi.oi_calls

  let allowed_s oi = allowed oi |> Sx.of_list

  let cost_self (oi : 'a t) =
    omap_dfl (fun (self,_) -> `Bounded self) `Unbounded oi.oi_costs

  let cost (oi : 'a t) (x : xpath) =
    omap_dfl (fun (_,oi) ->
        let c = Mx.find_opt x oi in
        omap_dfl (fun c -> `Bounded c) `Zero c)
      `Unbounded oi.oi_costs

  let cost_calls oi = omap_dfl (fun (_,x) -> `Bounded x) `Unbounded oi.oi_costs

  let costs oi = omap_dfl (fun x -> `Bounded x) `Unbounded oi.oi_costs

  let mk oi_calls oi_in oi_costs = match oi_costs with
    | `Bounded oi_costs ->
      { oi_calls; oi_in; oi_costs = Some (oi_costs) ; }
    | `Unbounded ->
      { oi_calls; oi_in; oi_costs = None; }

  (* let change_calls oi calls =
   *   mk calls oi.oi_in
   *     (Mx.filter (fun x _ -> List.mem x calls) oi.oi_costs) *)

  let filter f oi =
    let costs = match oi.oi_costs with
      | Some (self,costs) -> `Bounded (self, Mx.filter (fun x _ -> f x) costs)
      | None -> `Unbounded in
    mk (List.filter f oi.oi_calls) oi.oi_in costs

  let equal a_equal oi1 oi2 =
    let check_costs_eq c1 c2 =
      match c1,c2 with
      | None, None -> true
      | Some _, None | None, Some _ -> false
      | Some (s1,c1), Some (s2,c2) ->
        let exception Not_equal in
        try Mx.fold2_union (fun _ a b () -> match a, b with
            | Some _, None | None, Some _ -> raise Not_equal
            | None, None -> ()
            | Some a, Some b -> if a_equal a b then () else raise Not_equal
          ) c1 c2 ();
          a_equal s1 s2
        with Not_equal -> false in

    oi1.oi_in = oi2.oi_in
    && List.all2 EcPath.x_equal oi1.oi_calls oi1.oi_calls
    && check_costs_eq oi1.oi_costs oi2.oi_costs

  let hash ahash oi =
    let costs_hash =
      Why3.Hashcons.combine_option (fun (self,costs) ->
          (Why3.Hashcons.combine_list
             (Why3.Hashcons.combine_pair EcPath.x_hash ahash)
             (ahash self) (Mx.bindings costs))) oi.oi_costs in

    Why3.Hashcons.combine2
      (if oi.oi_in then 0 else 1)
      (Why3.Hashcons.combine_list EcPath.x_hash 0
         (List.sort EcPath.x_compare oi.oi_calls))
      costs_hash
end

(* -------------------------------------------------------------------- *)
type mr_xpaths = EcPath.Sx.t use_restr

type mr_mpaths = EcPath.Sm.t use_restr

type 'a p_mod_restr = {
  mr_xpaths : mr_xpaths;
  mr_mpaths : mr_mpaths;
  mr_oinfos : 'a PreOI.t Msym.t;
}

let p_mr_equal a_equal mr1 mr2 =
  ur_equal EcPath.Sx.equal mr1.mr_xpaths mr2.mr_xpaths
  && ur_equal EcPath.Sm.equal mr1.mr_mpaths mr2.mr_mpaths
  && Msym.equal (PreOI.equal a_equal) mr1.mr_oinfos mr2.mr_oinfos

let has_compl_restriction mr =
  Msym.exists (fun _ oi -> (PreOI.costs oi) <> `Unbounded) mr.mr_oinfos

let mr_is_empty mr =
     not (has_compl_restriction mr)
  && Msym.for_all (fun _ oi -> [] = PreOI.allowed oi && PreOI.is_in oi) mr.mr_oinfos

let mr_xpaths_fv (m : mr_xpaths) : int Mid.t =
  EcPath.Sx.fold
    (fun xp fv -> EcPath.x_fv fv xp)
    (Sx.union
       m.ur_neg
       (EcUtils.odfl Sx.empty m.ur_pos))
    EcIdent.Mid.empty

let mr_mpaths_fv (m : mr_mpaths) : int Mid.t =
  EcPath.Sm.fold
    (fun mp fv -> EcPath.m_fv fv mp)
    (Sm.union
       m.ur_neg
       (EcUtils.odfl Sm.empty m.ur_pos))
    EcIdent.Mid.empty

(* -------------------------------------------------------------------- *)
type funsig = {
  fs_name   : symbol;
  fs_arg    : EcTypes.ty;
  fs_anames : ovariable list;
  fs_ret    : EcTypes.ty;
}

let fs_equal f1 f2 =
    List.all2 EcTypes.ov_equal f1.fs_anames f2.fs_anames
    && (EcTypes.ty_equal f1.fs_ret f2.fs_ret)
    && (EcTypes.ty_equal f1.fs_arg f2.fs_arg)
    && (EcSymbols.sym_equal f1.fs_name f2.fs_name)

(* -------------------------------------------------------------------- *)
type 'a p_module_type = {
  mt_params : (EcIdent.t * 'a p_module_type) list;
  mt_name   : EcPath.path;
  mt_args   : EcPath.mpath list;
  mt_restr  : 'a p_mod_restr;
}

type module_sig_body_item = Tys_function of funsig

type module_sig_body = module_sig_body_item list

type 'a p_module_sig = {
  mis_params : (EcIdent.t * 'a p_module_type) list;
  mis_body   : module_sig_body;
  mis_restr  : 'a p_mod_restr;
}

type 'a p_top_module_sig = {
  tms_sig  : 'a p_module_sig;
  tms_loca : is_local;
}

(* -------------------------------------------------------------------- *)
(* Simple module signature, without restrictions. *)
type 'a p_module_smpl_sig = {
  miss_params : (EcIdent.t * 'a p_module_type) list;
  miss_body   : module_sig_body;
}

let sig_smpl_sig_coincide msig smpl_sig =
  let eqparams =
    List.for_all2 EcIdent.id_equal
      (List.map fst msig.mis_params)
      (List.map fst smpl_sig.miss_params) in

  let ls =
    List.map (fun (Tys_function fs) -> fs.fs_name, fs ) msig.mis_body
    |> EcSymbols.Msym.of_list
  and ls_smpl =
    List.map (fun (Tys_function fs) -> fs.fs_name, fs ) smpl_sig.miss_body
    |> EcSymbols.Msym.of_list in
  let eqsig =
    Msym.fold2_union (fun _ aopt bopt eqsig -> match aopt, bopt with
        | Some fs1, Some fs2 -> (fs_equal fs1 fs2) && eqsig
        | _ -> false)  ls_smpl ls true; in

  eqparams && eqsig

(* -------------------------------------------------------------------- *)
type uses = {
  us_calls  : xpath list;
  us_reads  : Sx.t;
  us_writes : Sx.t;
}

let mk_uses c r w =
  let map s = Sx.fold (fun x s ->
      Sx.change
        (fun b -> assert (not b); true)
        (EcTypes.xp_glob x) s) s Sx.empty in
  {us_calls = c; us_reads = map r; us_writes = map w }

(* -------------------------------------------------------------------- *)
type function_def = {
  f_locals : variable list;
  f_body   : stmt;
  f_ret    : EcTypes.expr option;
  f_uses   : uses;
}

let fd_equal f1 f2 =
     (s_equal f1.f_body f2.f_body)
  && (EcUtils.opt_equal EcTypes.e_equal f1.f_ret f2.f_ret)
  && (List.all2 EcTypes.v_equal f1.f_locals f2.f_locals)

let fd_hash f =
  Why3.Hashcons.combine2
    (s_hash f.f_body)
    (Why3.Hashcons.combine_option EcTypes.e_hash f.f_ret)
    (Why3.Hashcons.combine_list EcTypes.v_hash 0 f.f_locals)

(* -------------------------------------------------------------------- *)
type 'a p_function_body =
| FBdef   of function_def
| FBalias of xpath
| FBabs   of 'a PreOI.t

type 'a p_function_ = {
  f_name   : symbol;
  f_sig    : funsig;
  f_def    : 'a p_function_body;
}

(* -------------------------------------------------------------------- *)
type abs_uses = {
  aus_calls  : EcPath.xpath list;
  aus_reads  : (EcTypes.prog_var * EcTypes.ty) list;
  aus_writes : (EcTypes.prog_var * EcTypes.ty) list;
}

type 'a p_module_expr = {
  me_name     : symbol;
  me_body     : 'a p_module_body;
  me_comps    : 'a p_module_comps;
  me_sig_body : module_sig_body;
  me_params   : (EcIdent.t * 'a p_module_type) list;
}

(* Invariant:
   In an abstract module [ME_Decl mt], [mt] must not be a functor, i.e. it must
   be fully applied. Therefore, we must have:
   [List.length mp.mt_params = List.length mp.mt_args]  *)
and 'a p_module_body =
  | ME_Alias       of int * EcPath.mpath
  | ME_Structure   of 'a p_module_structure       (* Concrete modules. *)
  | ME_Decl        of 'a p_module_type         (* Abstract modules. *)

and 'a p_module_structure = {
  ms_body      : 'a p_module_item list;
}

and 'a p_module_item =
  | MI_Module   of 'a p_module_expr
  | MI_Variable of variable
  | MI_Function of 'a p_function_

and 'a p_module_comps = 'a p_module_comps_item list

and 'a p_module_comps_item = 'a p_module_item

type 'a p_top_module_expr = {
  tme_expr : 'a p_module_expr;
  tme_loca : locality;
}

(* -------------------------------------------------------------------- *)
let ur_hash elems el_hash ur =
  Why3.Hashcons.combine
    (Why3.Hashcons.combine_option
       (fun l -> Why3.Hashcons.combine_list el_hash 0 (elems l))
       ur.ur_pos)
    (Why3.Hashcons.combine_list el_hash 0
       (elems ur.ur_neg))

let p_mr_hash a_hash mr =
  Why3.Hashcons.combine2
    (ur_hash EcPath.Sx.ntr_elements EcPath.x_hash mr.mr_xpaths)
    (ur_hash EcPath.Sm.ntr_elements EcPath.m_hash mr.mr_mpaths)
    (Why3.Hashcons.combine_list
       (Why3.Hashcons.combine_pair Hashtbl.hash (PreOI.hash a_hash)) 0
       (EcSymbols.Msym.bindings mr.mr_oinfos
        |> List.sort (fun (s,_) (s',_) -> EcSymbols.sym_compare s s')))

let p_mty_hash a_hash mty =
  Why3.Hashcons.combine3
    (EcPath.p_hash mty.mt_name)
    (Why3.Hashcons.combine_list
       (fun (x, _) -> EcIdent.id_hash x)
       0 mty.mt_params)
    (Why3.Hashcons.combine_list EcPath.m_hash 0 mty.mt_args)
    (p_mr_hash a_hash mty.mt_restr)

let rec p_mty_equal a_equal mty1 mty2 =
     (EcPath.p_equal mty1.mt_name mty2.mt_name)
  && (List.all2 EcPath.m_equal mty1.mt_args mty2.mt_args)
  && (List.all2 (pair_equal EcIdent.id_equal (p_mty_equal a_equal))
        mty1.mt_params mty2.mt_params)
  && (p_mr_equal a_equal mty1.mt_restr mty2.mt_restr)

(* -------------------------------------------------------------------- *)
let get_uninit_read_of_fun (f : _ p_function_) =
  match f.f_def with
  | FBalias _ | FBabs _ -> Ssym.empty

  | FBdef fd ->
      let w =
        let toloc ov =
          (* We don't allow anonymous parameters on concrete procedures *)
          assert (is_some ov.ov_name);
          oget ov.ov_name
        in
        let w = List.map toloc f.f_sig.fs_anames in
        Ssym.of_list w
      in

      let w, r  = s_get_uninit_read w fd.f_body in
      let raout = fd.f_ret |> omap (Uninit.e_pv) in
      let raout = Ssym.diff (raout |> odfl Ssym.empty) w in
      Ssym.union r raout

(* -------------------------------------------------------------------- *)
let get_uninit_read_of_module (p : path) (me : _ p_module_expr) =
  let rec doit_me acc (mp, me) =
    match me.me_body with
    | ME_Alias     _  -> acc
    | ME_Decl      _  -> acc
    | ME_Structure mb -> doit_mb acc (mp, mb)

  and doit_mb acc (mp, mb) =
    List.fold_left
      (fun acc item -> doit_mb1 acc (mp, item))
      acc mb.ms_body

  and doit_mb1 acc (mp, item) =
    match item with
    | MI_Module subme ->
        doit_me acc (EcPath.mqname mp subme.me_name, subme)

    | MI_Variable _ ->
        acc

    | MI_Function f ->
        let xp = xpath mp f.f_name in
        let r  = get_uninit_read_of_fun f in
        if Ssym.is_empty r then acc else (xp, r) :: acc

  in

  let mp =
    let margs =
      List.map
        (fun (x, _) -> EcPath.mpath_abs x [])
        me.me_params
    in EcPath.mpath_crt (EcPath.pqname p me.me_name) margs None

  in List.rev (doit_me [] (mp, me))
