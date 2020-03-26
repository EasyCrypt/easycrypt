(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

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
let i_assert   e            = mk_instr (Sassert e)
let i_abstract id           = mk_instr (Sabstract id)

let s_seq      s1 s2        = stmt (s1.s_node @ s2.s_node)
let s_empty                 = stmt []

let s_asgn     arg = stmt [i_asgn arg]
let s_rnd      arg = stmt [i_rnd arg]
let s_call     arg = stmt [i_call arg]
let s_if       arg = stmt [i_if arg]
let s_while    arg = stmt [i_while arg]
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
let destr_assert = _destr_of_get get_assert

(* -------------------------------------------------------------------- *)
let _is_of_get (get : instr -> 'a option) (i : instr) =
  EcUtils.is_some (get i)

let is_asgn   = _is_of_get get_asgn
let is_rnd    = _is_of_get get_rnd
let is_call   = _is_of_get get_call
let is_if     = _is_of_get get_if
let is_while  = _is_of_get get_while
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
  type i_assert   = EcTypes.expr
  type i_abstract = EcIdent.t

  val i_asgn     : (instr * i_asgn    ) -> i_asgn     -> instr
  val i_rnd      : (instr * i_rnd     ) -> i_rnd      -> instr
  val i_call     : (instr * i_call    ) -> i_call     -> instr
  val i_if       : (instr * i_if      ) -> i_if       -> instr
  val i_while    : (instr * i_while   ) -> i_while    -> instr
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
  type i_assert   = EcTypes.expr
  type i_abstract = EcIdent.t
  type s_stmt     = instr list

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

  let i_assert (i, e) e' =
    if e == e' then i else i_assert e'

  let i_abstract (i, x) x' =
    if x == x' then i else i_abstract x

  let s_stmt s is' =
    if s.s_node == is' then s else stmt is'
end

(* -------------------------------------------------------------------- *)
let s_subst (s : EcTypes.e_subst) =
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

    | Sassert e ->
        ISmart.i_assert (i, e) (e_subst e)

    | Sabstract _ ->
        i

  and s_subst s =
    ISmart.s_stmt s (List.Smart.map i_subst s.s_node)

  in s_subst

(* -------------------------------------------------------------------- *)
module Uninit = struct    (* FIXME: generalize this for use in ecPV *)
  let e_pv =
    let rec e_pv tx sx e =
      match e.e_node with
      | Evar pv ->
          if tx pv then Sx.add (xastrip pv.pv_name) sx else sx
      | _ ->
          e_fold (e_pv tx) sx e
    in fun tx e -> e_pv tx Sx.empty e
end

let rec lv_get_uninit_read (w : Sx.t) (lv : lvalue) =
  let sx_of_pv pv =
    if is_loc pv then Sx.singleton (xastrip pv.pv_name) else Sx.empty
  in

  match lv with
  | LvVar (x, _) ->
      Sx.union (sx_of_pv x) w

  | LvTuple xs ->
      let w' = List.map (sx_of_pv |- fst) xs in
      Sx.big_union (w :: w')

and s_get_uninit_read (w : Sx.t) (s : stmt) =
  let do1 (w, r) i =
    let w, r' = i_get_uninit_read w i in
    (w, Sx.union r r')

  in List.fold_left do1 (w, Sx.empty) s.s_node

and i_get_uninit_read (w : Sx.t) (i : instr) =
  match i.i_node with
  | Sasgn (lv, e) | Srnd (lv, e) ->
      let r1 = Sx.diff (Uninit.e_pv is_loc e) w in
      let w2 = lv_get_uninit_read w lv in
      (Sx.union w w2, r1)

  | Scall (olv, _, args) ->
      let r1    = Sx.diff (Sx.big_union (List.map (Uninit.e_pv is_loc) args)) w in
      let w = olv |> omap (lv_get_uninit_read w) |> odfl w in
      (w, r1)

  | Sif (e, s1, s2) ->
      let r = Sx.diff (Uninit.e_pv is_loc e) w in
      let w1, r1 = s_get_uninit_read w s1 in
      let w2, r2 = s_get_uninit_read w s2 in
      (Sx.union w (Sx.inter w1 w2), Sx.big_union [r; r1; r2])

  | Swhile (e, s) ->
      let r  = Sx.diff (Uninit.e_pv is_loc e) w in
      let rs = snd (s_get_uninit_read w s) in
      (w, Sx.union r rs)

  | Sassert e ->
      (w, Sx.diff (Uninit.e_pv is_loc e) w)

  | Sabstract (_ : EcIdent.t) ->
      (w, Sx.empty)

let get_uninit_read (s : stmt) =
  snd (s_get_uninit_read Sx.empty s)

(* -------------------------------------------------------------------- *)
type variable = {
  v_name : symbol;
  v_type : EcTypes.ty;
}

let v_name { v_name = x } = x
let v_type { v_type = x } = x

(* -------------------------------------------------------------------- *)
type funsig = {
  fs_name   : symbol;
  fs_arg    : EcTypes.ty;
  fs_anames : variable list option;
  fs_ret    : EcTypes.ty;
}

(* -------------------------------------------------------------------- *)
type oracle_info = {
  oi_calls : xpath list;
  oi_in    : bool;
}

type module_type = {
  mt_params : (EcIdent.t * module_type) list;
  mt_name   : EcPath.path;
  mt_args   : EcPath.mpath list;
}

type module_sig_body_item =
| Tys_function of funsig * oracle_info

type module_sig_body = module_sig_body_item list

type module_sig = {
  mis_params : (EcIdent.t * module_type) list;
  mis_body   : module_sig_body;
}

(* -------------------------------------------------------------------- *)
type uses = {
  us_calls  : xpath list;
  us_reads  : Sx.t;
  us_writes : Sx.t;
}

let mk_uses c r w =
  let map s = Sx.fold (fun x s -> Sx.add (EcTypes.xp_glob x) s) s Sx.empty in
  {us_calls = c; us_reads = map r; us_writes = map w }


type function_def = {
  f_locals : variable list;
  f_body   : stmt;
  f_ret    : EcTypes.expr option;
  f_uses   : uses;
}

type function_body =
| FBdef   of function_def
| FBalias of xpath
| FBabs   of oracle_info

type function_ = {
  f_name   : symbol;
  f_sig    : funsig;
  f_def    : function_body;
}

(* -------------------------------------------------------------------- *)
type abs_uses = {
  aus_calls  : EcPath.xpath list;
  aus_reads  : (EcTypes.prog_var * EcTypes.ty) list;
  aus_writes : (EcTypes.prog_var * EcTypes.ty) list;
}

(* -------------------------------------------------------------------- *)
type mod_restr = EcPath.Sx.t * EcPath.Sm.t

let mr_equal (rx1,r1) (rx2,r2) =
  EcPath.Sx.equal rx1 rx2 && EcPath.Sm.equal r1 r2

type module_expr = {
  me_name      : symbol;
  me_body      : module_body;
  me_comps     : module_comps;
  me_sig       : module_sig;
}

and module_body =
  | ME_Alias       of int * EcPath.mpath
  | ME_Structure   of module_structure
  | ME_Decl        of module_type * mod_restr

and module_structure = {
  ms_body : module_item list;
}

and module_item =
  | MI_Module   of module_expr
  | MI_Variable of variable
  | MI_Function of function_

and module_comps = module_comps_item list

and module_comps_item = module_item

(* -------------------------------------------------------------------- *)
let vd_equal vd1 vd2 =
  vd1.v_name = vd2.v_name &&
  EcTypes.ty_equal vd1.v_type vd2.v_type

let vd_hash vd =
  Why3.Hashcons.combine (Hashtbl.hash vd.v_name) (EcTypes.ty_hash vd.v_type)

let fd_equal f1 f2 =
     (s_equal f1.f_body f2.f_body)
  && (EcUtils.opt_equal EcTypes.e_equal f1.f_ret f2.f_ret)
  && (List.all2 vd_equal f1.f_locals f2.f_locals)

let fd_hash f =
  Why3.Hashcons.combine2
    (s_hash f.f_body)
    (Why3.Hashcons.combine_option EcTypes.e_hash f.f_ret)
    (Why3.Hashcons.combine_list vd_hash 0 f.f_locals)

(* -------------------------------------------------------------------- *)
let rec mty_subst sp sm mty =
  let mt_params = List.map (snd_map (mty_subst sp sm)) mty.mt_params in
  let mt_name   = sp mty.mt_name in
  let mt_args   = List.map sm mty.mt_args in
  { mt_params; mt_name; mt_args; }

let mty_hash mty =
  Why3.Hashcons.combine2
    (EcPath.p_hash mty.mt_name)
    (Why3.Hashcons.combine_list
       (fun (x, _) -> EcIdent.id_hash x)
       0 mty.mt_params)
    (Why3.Hashcons.combine_list EcPath.m_hash 0 mty.mt_args)

let rec mty_equal mty1 mty2 =
     (EcPath.p_equal mty1.mt_name mty2.mt_name)
  && (List.all2 EcPath.m_equal mty1.mt_args mty2.mt_args)
  && (List.all2 (pair_equal EcIdent.id_equal mty_equal) mty1.mt_params mty2.mt_params)

(* -------------------------------------------------------------------- *)
let get_uninit_read_of_fun (fp : xpath) (f : function_) =
  match f.f_def with
  | FBalias _ | FBabs _ -> Sx.empty

  | FBdef fd ->
      let w =
        let toloc { v_name = x } = (EcTypes.pv_loc fp x).pv_name in
        let w = List.map toloc (f.f_sig.fs_anames |> odfl []) in
        Sx.of_list (List.map xastrip w)
      in

      let w, r  = s_get_uninit_read w fd.f_body in
      let raout = fd.f_ret |> omap (Uninit.e_pv is_loc) in
      let raout = Sx.diff (raout |> odfl Sx.empty) w in
      Sx.union r raout

(* -------------------------------------------------------------------- *)
let get_uninit_read_of_module (p : path) (me : module_expr) =
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
        let xp = xpath_fun mp f.f_name in
        let r  = get_uninit_read_of_fun xp f in
        if Sx.is_empty r then acc else (xp, r) :: acc

  in

  let mp =
    let margs =
      List.map
        (fun (x, _) -> EcPath.mpath_abs x [])
        me.me_sig.mis_params
    in EcPath.mpath_crt (EcPath.pqname p me.me_name) margs None

  in List.rev (doit_me [] (mp, me))
