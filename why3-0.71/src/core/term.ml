(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2011                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

open Util
open Ident
open Ty

(** Variable symbols *)

type vsymbol = {
  vs_name : ident;
  vs_ty   : ty;
}

module Vsym = WeakStructMake (struct
  type t = vsymbol
  let tag vs = vs.vs_name.id_tag
end)

module Svs = Vsym.S
module Mvs = Vsym.M
module Hvs = Vsym.H

let vs_equal : vsymbol -> vsymbol -> bool = (==)

let vs_hash vs = id_hash vs.vs_name

let create_vsymbol name ty = {
  vs_name = id_register name;
  vs_ty   = ty;
}

(** Function and predicate symbols *)

type lsymbol = {
  ls_name   : ident;
  ls_args   : ty list;
  ls_value  : ty option;
}

module Lsym = WeakStructMake (struct
  type t = lsymbol
  let tag ls = ls.ls_name.id_tag
end)

module Sls = Lsym.S
module Mls = Lsym.M
module Hls = Lsym.H
module Wls = Lsym.W

let ls_equal : lsymbol -> lsymbol -> bool = (==)

let ls_hash ls = id_hash ls.ls_name

let create_lsymbol name args value = {
  ls_name   = id_register name;
  ls_args   = args;
  ls_value  = value;
}

let create_fsymbol nm al vl = create_lsymbol nm al (Some vl)
let create_psymbol nm al    = create_lsymbol nm al (None)

let ls_ty_freevars ls =
  let acc = oty_freevars Stv.empty ls.ls_value in
  List.fold_left ty_freevars acc ls.ls_args

(** Patterns *)

type pattern = {
  pat_node : pattern_node;
  pat_vars : Svs.t;
  pat_ty   : ty;
  pat_tag  : int;
}

and pattern_node =
  | Pwild
  | Pvar of vsymbol
  | Papp of lsymbol * pattern list
  | Por  of pattern * pattern
  | Pas  of pattern * vsymbol

let pat_equal : pattern -> pattern -> bool = (==)

let pat_hash p = p.pat_tag

module Hspat = Hashcons.Make (struct
  type t = pattern

  let equal_node p1 p2 = match p1, p2 with
    | Pwild, Pwild -> true
    | Pvar v1, Pvar v2 -> vs_equal v1 v2
    | Papp (s1, l1), Papp (s2, l2) ->
        ls_equal s1 s2 && List.for_all2 pat_equal l1 l2
    | Por (p1, q1), Por (p2, q2) ->
        pat_equal p1 p2 && pat_equal q1 q2
    | Pas (p1, n1), Pas (p2, n2) ->
        pat_equal p1 p2 && vs_equal n1 n2
    | _ -> false

  let equal p1 p2 =
    equal_node p1.pat_node p2.pat_node && ty_equal p1.pat_ty p2.pat_ty

  let hash_node = function
    | Pwild -> 0
    | Pvar v -> vs_hash v
    | Papp (s, pl) -> Hashcons.combine_list pat_hash (ls_hash s) pl
    | Por (p, q) -> Hashcons.combine (pat_hash p) (pat_hash q)
    | Pas (p, v) -> Hashcons.combine (pat_hash p) (vs_hash v)

  let hash p = Hashcons.combine (hash_node p.pat_node) (ty_hash p.pat_ty)

  let tag n p = { p with pat_tag = n }
end)

module Pat = StructMake (struct
  type t = pattern
  let tag pat = pat.pat_tag
end)

module Spat = Pat.S
module Mpat = Pat.M
module Hpat = Pat.H

(* h-consing constructors for patterns *)

let mk_pattern n vs ty = Hspat.hashcons {
  pat_node = n;
  pat_vars = vs;
  pat_ty   = ty;
  pat_tag  = -1
}

exception UncoveredVar of vsymbol
exception DuplicateVar of vsymbol

let pat_wild ty = mk_pattern Pwild Svs.empty ty
let pat_var v   = mk_pattern (Pvar v) (Svs.singleton v) v.vs_ty

let pat_as p v =
  let s = Svs.add_new v (DuplicateVar v) p.pat_vars in
  mk_pattern (Pas (p,v)) s v.vs_ty

let pat_or p q =
  if Svs.equal p.pat_vars q.pat_vars then
    mk_pattern (Por (p,q)) p.pat_vars p.pat_ty
  else
    let s = Mvs.union (fun _ _ _ -> None) p.pat_vars q.pat_vars in
    raise (UncoveredVar (Svs.choose s))

let pat_app f pl ty =
  let dup v () () = raise (DuplicateVar v) in
  let merge s p = Mvs.union dup s p.pat_vars in
  mk_pattern (Papp (f,pl)) (List.fold_left merge Svs.empty pl) ty

(* generic traversal functions *)

let pat_map fn pat = match pat.pat_node with
  | Pwild | Pvar _ -> pat
  | Papp (s, pl) -> pat_app s (List.map fn pl) pat.pat_ty
  | Pas (p, v) -> pat_as (fn p) v
  | Por (p, q) -> pat_or (fn p) (fn q)

let pat_map fn = pat_map (fun p ->
  let res = fn p in ty_equal_check p.pat_ty res.pat_ty; res)

let pat_fold fn acc pat = match pat.pat_node with
  | Pwild | Pvar _ -> acc
  | Papp (_, pl) -> List.fold_left fn acc pl
  | Pas (p, _) -> fn acc p
  | Por (p, q) -> fn (fn acc p) q

let pat_all pr pat = try pat_fold (all_fn pr) true pat with FoldSkip -> false
let pat_any pr pat = try pat_fold (any_fn pr) false pat with FoldSkip -> true

(* smart constructors for patterns *)

exception BadArity of lsymbol * int * int
exception FunctionSymbolExpected of lsymbol
exception PredicateSymbolExpected of lsymbol

let pat_app fs pl ty =
  let s = match fs.ls_value with
    | Some vty -> ty_match Mtv.empty vty ty
    | None -> raise (FunctionSymbolExpected fs)
  in
  let mtch s ty p = ty_match s ty p.pat_ty in
  ignore (try List.fold_left2 mtch s fs.ls_args pl
    with Invalid_argument _ -> raise (BadArity
      (fs, List.length fs.ls_args, List.length pl)));
  pat_app fs pl ty

let pat_as p v =
  ty_equal_check p.pat_ty v.vs_ty;
  pat_as p v

let pat_or p q =
  ty_equal_check p.pat_ty q.pat_ty;
  pat_or p q

(* rename all variables in a pattern *)

let rec pat_rename_all m p = match p.pat_node with
  | Pvar v -> pat_var (Mvs.find v m)
  | Pas (p, v) -> pat_as (pat_rename_all m p) (Mvs.find v m)
  | _ -> pat_map (pat_rename_all m) p

(* symbol-wise map/fold *)

let rec pat_gen_map fnT fnL m pat =
  let fn = pat_gen_map fnT fnL m in
  let ty = fnT pat.pat_ty in
  match pat.pat_node with
    | Pwild -> pat_wild ty
    | Pvar v -> pat_var (Mvs.find v m)
    | Papp (s, pl) -> pat_app (fnL s) (List.map fn pl) ty
    | Pas (p, v) -> pat_as (fn p) (Mvs.find v m)
    | Por (p, q) -> pat_or (fn p) (fn q)

let rec pat_gen_fold fnT fnL acc pat =
  let fn acc p = pat_gen_fold fnT fnL acc p in
  let acc = fnT acc pat.pat_ty in
  match pat.pat_node with
    | Pwild | Pvar _ -> acc
    | Papp (s, pl) -> List.fold_left fn (fnL acc s) pl
    | Por (p, q) -> fn (fn acc p) q
    | Pas (p, _) -> fn acc p

(** Terms and formulas *)

type quant =
  | Tforall
  | Texists

type binop =
  | Tand
  | Tor
  | Timplies
  | Tiff

type integer_constant =
  | IConstDecimal of string
  | IConstHexa of string
  | IConstOctal of string
  | IConstBinary of string

type real_constant =
  | RConstDecimal of string * string * string option (* int / frac / exp *)
  | RConstHexa of string * string * string

type constant =
  | ConstInt of integer_constant
  | ConstReal of real_constant

type term = {
  t_node  : term_node;
  t_ty    : ty option;
  t_label : label list;
  t_loc   : Loc.position option;
  t_vars  : int Mvs.t;
  t_tag   : int;
}

and term_node =
  | Tvar of vsymbol
  | Tconst of constant
  | Tapp of lsymbol * term list
  | Tif of term * term * term
  | Tlet of term * term_bound
  | Tcase of term * term_branch list
  | Teps of term_bound
  | Tquant of quant * term_quant
  | Tbinop of binop * term * term
  | Tnot of term
  | Ttrue
  | Tfalse

and term_bound  = vsymbol * bind_info * term
and term_branch = pattern * bind_info * term
and term_quant  = vsymbol list * bind_info * trigger * term

and trigger = term list list

and bind_info = {
  bv_vars  : int Mvs.t;   (* free variables *)
  bv_subst : term Mvs.t   (* deferred substitution *)
}

(* term equality and hash *)

let t_equal : term -> term -> bool = (==)
let t_hash t = t.t_tag

(* type checking *)

exception TermExpected of term
exception FmlaExpected of term

let t_type t = match t.t_ty with
  | Some ty -> ty
  | None -> raise (TermExpected t)

let t_prop f =
  if f.t_ty = None then f else raise (FmlaExpected f)

let t_ty_check t ty = match ty, t.t_ty with
  | Some l, Some r -> ty_equal_check l r
  | Some _, None -> raise (TermExpected t)
  | None, Some _ -> raise (FmlaExpected t)
  | None, None -> ()

let vs_check v t = ty_equal_check v.vs_ty (t_type t)

(* trigger equality and traversal *)

let tr_equal = list_all2 (list_all2 t_equal)

let tr_map fn = List.map (List.map fn)
let tr_fold fn = List.fold_left (List.fold_left fn)
let tr_map_fold fn = Util.map_fold_left (Util.map_fold_left fn)

(* bind_info equality, hash, and traversal *)

let bnd_equal b1 b2 = Mvs.equal t_equal b1.bv_subst b2.bv_subst

let bnd_hash bv =
  let comb v t acc = Hashcons.combine2 (vs_hash v) (t_hash t) acc in
  Mvs.fold comb bv.bv_subst

let bnd_map fn bv = { bv with bv_subst = Mvs.map fn bv.bv_subst }

let bnd_fold fn acc bv = Mvs.fold (fun _ t a -> fn a t) bv.bv_subst acc

let bnd_map_fold fn acc bv =
  let acc,s = Mvs.mapi_fold (fun _ t a -> fn a t) bv.bv_subst acc in
  acc, { bv with bv_subst = s }

(* hash-consing for terms and formulas *)

let some_plus _ m n = Some (m + n)
let add_t_vars s t = Mvs.union some_plus s t.t_vars
let add_b_vars s (_,b,_) = Mvs.union some_plus s b.bv_vars
let add_nt_vars _ n t s = Mvs.union some_plus s
  (if n = 1 then t.t_vars else Mvs.map (( * ) n) t.t_vars)

module Hsterm = Hashcons.Make (struct

  type t = term

  let t_eq_bound (v1,b1,t1) (v2,b2,t2) =
    vs_equal v1 v2 && bnd_equal b1 b2 && t_equal t1 t2

  let t_eq_branch (p1,b1,t1) (p2,b2,t2) =
    pat_equal p1 p2 && bnd_equal b1 b2 && t_equal t1 t2

  let t_eq_quant (vl1,b1,tl1,f1) (vl2,b2,tl2,f2) =
    t_equal f1 f2 && list_all2 vs_equal vl1 vl2 &&
    bnd_equal b1 b2 && tr_equal tl1 tl2

  let t_equal_node t1 t2 = match t1,t2 with
    | Tvar v1, Tvar v2 -> vs_equal v1 v2
    | Tconst c1, Tconst c2 -> c1 = c2
    | Tapp (s1,l1), Tapp (s2,l2) ->
        ls_equal s1 s2 && List.for_all2 t_equal l1 l2
    | Tif (f1,t1,e1), Tif (f2,t2,e2) ->
        t_equal f1 f2 && t_equal t1 t2 && t_equal e1 e2
    | Tlet (t1,b1), Tlet (t2,b2) ->
        t_equal t1 t2 && t_eq_bound b1 b2
    | Tcase (t1,bl1), Tcase (t2,bl2) ->
        t_equal t1 t2 && list_all2 t_eq_branch bl1 bl2
    | Teps f1, Teps f2 -> t_eq_bound f1 f2
    | Tquant (q1,b1), Tquant (q2,b2) ->
        q1 = q2 && t_eq_quant b1 b2
    | Tbinop (op1,f1,g1), Tbinop (op2,f2,g2) ->
        op1 = op2 && t_equal f1 f2 && t_equal g1 g2
    | Tnot f1, Tnot f2 -> t_equal f1 f2
    | Ttrue, Ttrue | Tfalse, Tfalse -> true
    | _ -> false

  let equal t1 t2 =
    oty_equal t1.t_ty t2.t_ty &&
    t_equal_node t1.t_node t2.t_node &&
    list_all2 (=) t1.t_label t2.t_label &&
    option_eq Loc.equal t1.t_loc t2.t_loc

  let t_hash_bound (v,b,t) =
    Hashcons.combine (vs_hash v) (bnd_hash b (t_hash t))

  let t_hash_branch (p,b,t) =
    Hashcons.combine (pat_hash p) (bnd_hash b (t_hash t))

  let t_hash_quant (vl,b,tl,f) =
    let h = bnd_hash b (t_hash f) in
    let h = Hashcons.combine_list vs_hash h vl in
    List.fold_left (Hashcons.combine_list t_hash) h tl

  let t_hash_node = function
    | Tvar v -> vs_hash v
    | Tconst c -> Hashtbl.hash c
    | Tapp (f,tl) -> Hashcons.combine_list t_hash (ls_hash f) tl
    | Tif (f,t,e) -> Hashcons.combine2 (t_hash f) (t_hash t) (t_hash e)
    | Tlet (t,bt) -> Hashcons.combine (t_hash t) (t_hash_bound bt)
    | Tcase (t,bl) -> Hashcons.combine_list t_hash_branch (t_hash t) bl
    | Teps f -> t_hash_bound f
    | Tquant (q,bf) -> Hashcons.combine (Hashtbl.hash q) (t_hash_quant bf)
    | Tbinop (op,f1,f2) ->
        Hashcons.combine2 (Hashtbl.hash op) (t_hash f1) (t_hash f2)
    | Tnot f -> Hashcons.combine 1 (t_hash f)
    | Ttrue -> 0
    | Tfalse -> 1

  let hash t =
    Hashcons.combine2 (t_hash_node t.t_node)
      (Hashcons.combine_option Loc.hash t.t_loc)
      (Hashcons.combine_list Hashtbl.hash (oty_hash t.t_ty) t.t_label)

  let t_vars_node = function
    | Tvar v -> Mvs.singleton v 1
    | Tconst _ -> Mvs.empty
    | Tapp (_,tl) -> List.fold_left add_t_vars Mvs.empty tl
    | Tif (f,t,e) -> add_t_vars (add_t_vars f.t_vars t) e
    | Tlet (t,bt) -> add_b_vars t.t_vars bt
    | Tcase (t,bl) -> List.fold_left add_b_vars t.t_vars bl
    | Teps (_,b,_) -> b.bv_vars
    | Tquant (_,(_,b,_,_)) -> b.bv_vars
    | Tbinop (_,f1,f2) -> add_t_vars f1.t_vars f2
    | Tnot f -> f.t_vars
    | Ttrue | Tfalse -> Mvs.empty

  let tag n t = { t with t_tag = n ; t_vars = t_vars_node t.t_node }

end)

module Term = StructMake (struct
  type t = term
  let tag term = term.t_tag
end)

module Sterm = Term.S
module Mterm = Term.M
module Hterm = Term.H

(* hash-consing constructors for terms *)

let mk_term n ty = Hsterm.hashcons {
  t_node  = n;
  t_label = [];
  t_loc   = None;
  t_vars  = Mvs.empty;
  t_ty    = ty;
  t_tag   = -1
}

let t_var v         = mk_term (Tvar v) (Some v.vs_ty)
let t_const c ty    = mk_term (Tconst c) (Some ty)
let t_int_const s   = mk_term (Tconst (ConstInt (IConstDecimal s))) (Some Ty.ty_int)
let t_real_const r  = mk_term (Tconst (ConstReal r)) (Some Ty.ty_real)
let t_app f tl ty   = mk_term (Tapp (f, tl)) ty
let t_if f t1 t2    = mk_term (Tif (f, t1, t2)) t2.t_ty
let t_let t1 bt ty  = mk_term (Tlet (t1, bt)) ty
let t_case t1 bl ty = mk_term (Tcase (t1, bl)) ty
let t_eps bf ty     = mk_term (Teps bf) ty
let t_quant q qf    = mk_term (Tquant (q, qf)) None
let t_binary op f g = mk_term (Tbinop (op, f, g)) None
let t_not f         = mk_term (Tnot f) None
let t_true          = mk_term (Ttrue) None
let t_false         = mk_term (Tfalse) None

let t_label ?loc l t = Hsterm.hashcons { t with t_label = l; t_loc = loc }
let t_label_add  l t = Hsterm.hashcons { t with t_label = l :: t.t_label }

let t_label_copy { t_label = l; t_loc = p } t =
  if t.t_label = [] && t.t_loc = None && (l <> [] || p <> None)
  then t_label ?loc:p l t else t

(* unsafe map *)

let bound_map fn (u,b,e) = (u, bnd_map fn b, fn e)

let t_map_unsafe fn t = t_label_copy t (match t.t_node with
  | Tvar _ | Tconst _ -> t
  | Tapp (f,tl) ->
      let sl = List.map fn tl in
      if List.for_all2 t_equal sl tl then t else
      t_app f sl t.t_ty
  | Tif (f,t1,t2) ->
      let g = fn f and s1 = fn t1 and s2 = fn t2 in
      if t_equal g f && t_equal s1 t1 && t_equal s2 t2 then t else
      t_if g s1 s2
  | Tlet (e,b) ->
      t_let (fn e) (bound_map fn b) t.t_ty
  | Tcase (e,bl) ->
      t_case (fn e) (List.map (bound_map fn) bl) t.t_ty
  | Teps b ->
      t_eps (bound_map fn b) t.t_ty
  | Tquant (q,(vl,b,tl,f1)) ->
      t_quant q (vl, bnd_map fn b, tr_map fn tl, fn f1)
  | Tbinop (op,f1,f2) ->
      let g1 = fn f1 and g2 = fn f2 in
      if t_equal g1 f1 && t_equal g2 f2 then t else
      t_binary op g1 g2
  | Tnot f1 ->
      let g1 = fn f1 in
      if t_equal g1 f1 then t else
      t_not g1
  | Ttrue | Tfalse -> t)

(* unsafe fold *)

let bound_fold fn acc (_,b,e) = fn (bnd_fold fn acc b) e

let t_fold_unsafe fn acc t = match t.t_node with
  | Tvar _ | Tconst _ -> acc
  | Tapp (_,tl) -> List.fold_left fn acc tl
  | Tif (f,t1,t2) -> fn (fn (fn acc f) t1) t2
  | Tlet (e,b) -> fn (bound_fold fn acc b) e
  | Tcase (e,bl) -> List.fold_left (bound_fold fn) (fn acc e) bl
  | Teps b -> bound_fold fn acc b
  | Tquant (_,(_,b,tl,f1)) -> fn (tr_fold fn (bnd_fold fn acc b) tl) f1
  | Tbinop (_,f1,f2) -> fn (fn acc f1) f2
  | Tnot f1 -> fn acc f1
  | Ttrue | Tfalse -> acc

(* unsafe map_fold *)

let bound_map_fold fn acc (u,b,e) =
  let acc, b = bnd_map_fold fn acc b in
  let acc, e = fn acc e in
  acc, (u,b,e)

let t_map_fold_unsafe fn acc t = match t.t_node with
  | Tvar _ | Tconst _ ->
      acc, t
  | Tapp (f,tl) ->
      let acc,sl = map_fold_left fn acc tl in
      if List.for_all2 t_equal sl tl then acc,t else
      acc, t_label_copy t (t_app f sl t.t_ty)
  | Tif (f,t1,t2) ->
      let acc, g  = fn acc f in
      let acc, s1 = fn acc t1 in
      let acc, s2 = fn acc t2 in
      if t_equal g f && t_equal s1 t1 && t_equal s2 t2 then acc,t else
      acc, t_label_copy t (t_if g s1 s2)
  | Tlet (e,b) ->
      let acc, e = fn acc e in
      let acc, b = bound_map_fold fn acc b in
      acc, t_label_copy t (t_let e b t.t_ty)
  | Tcase (e,bl) ->
      let acc, e = fn acc e in
      let acc, bl = map_fold_left (bound_map_fold fn) acc bl in
      acc, t_label_copy t (t_case e bl t.t_ty)
  | Teps b ->
      let acc, b = bound_map_fold fn acc b in
      acc, t_label_copy t (t_eps b t.t_ty)
  | Tquant (q,(vl,b,tl,f1)) ->
      let acc, b = bnd_map_fold fn acc b in
      let acc, tl = tr_map_fold fn acc tl in
      let acc, f1 = fn acc f1 in
      acc, t_label_copy t (t_quant q (vl,b,tl,f1))
  | Tbinop (op,f1,f2) ->
      let acc, g1 = fn acc f1 in
      let acc, g2 = fn acc f2 in
      if t_equal g1 f1 && t_equal g2 f2 then acc,t else
      acc, t_label_copy t (t_binary op g1 g2)
  | Tnot f1 ->
      let acc, g1 = fn acc f1 in
      if t_equal g1 f1 then acc,t else
      acc, t_label_copy t (t_not g1)
  | Ttrue | Tfalse ->
      acc, t

(* type-unsafe term substitution *)

let rec t_subst_unsafe m t =
  let t_subst t = t_subst_unsafe m t in
  let b_subst (u,b,e) = (u, bv_subst_unsafe m b, e) in
  let nosubst (_,b,_) = Mvs.set_disjoint m b.bv_vars in
  match t.t_node with
  | Tvar u ->
      Mvs.find_default u t m
  | Tlet (e, bt) ->
      let d = t_subst e in
      if t_equal d e && nosubst bt then t else
      t_label_copy t (t_let d (b_subst bt) t.t_ty)
  | Tcase (e, bl) ->
      let d = t_subst e in
      if t_equal d e && List.for_all nosubst bl then t else
      let bl = List.map b_subst bl in
      t_label_copy t (t_case d bl t.t_ty)
  | Teps bf ->
      if nosubst bf then t else
      t_label_copy t (t_eps (b_subst bf) t.t_ty)
  | Tquant (q, (vl,b,tl,f1)) ->
      if Mvs.set_disjoint m b.bv_vars then t else
      let b = bv_subst_unsafe m b in
      t_label_copy t (t_quant q (vl,b,tl,f1))
  | _ ->
      t_map_unsafe t_subst t

and bv_subst_unsafe m b =
  (* restrict m to the variables free in b *)
  let m = Mvs.set_inter m b.bv_vars in
  (* if m is empty, return early *)
  if Mvs.is_empty m then b else
  (* remove from b.bv_vars the variables replaced by m *)
  let s = Mvs.set_diff b.bv_vars m in
  (* add to b.bv_vars the free variables added by m *)
  let s = Mvs.fold2_inter add_nt_vars b.bv_vars m s in
  (* apply m to the terms in b.bv_subst *)
  let h = Mvs.map (t_subst_unsafe m) b.bv_subst in
  (* join m to b.bv_subst *)
  let h = Mvs.union (fun _ _ t -> Some t) m h in
  (* reconstruct b *)
  { bv_vars = s ; bv_subst = h }

let t_subst_unsafe m t =
  if Mvs.is_empty m then t else t_subst_unsafe m t

(* close bindings *)

let bnd_new s = { bv_vars = s ; bv_subst = Mvs.empty }

let t_close_bound v t = (v, bnd_new (Mvs.remove v t.t_vars), t)

let t_close_branch p t = (p, bnd_new (Mvs.set_diff t.t_vars p.pat_vars), t)

let t_close_quant vl tl f =
  let del_v s v = Mvs.remove v s in
  let s = tr_fold add_t_vars f.t_vars tl in
  let s = List.fold_left del_v s vl in
  (vl, bnd_new s, tl, t_prop f)

(* open bindings *)

let fresh_vsymbol v =
  create_vsymbol (id_clone v.vs_name) v.vs_ty

let vs_rename h v =
  let u = fresh_vsymbol v in
  Mvs.add v (t_var u) h, u

let vl_rename h vl =
  Util.map_fold_left vs_rename h vl

let pat_rename h p =
  let add_vs v () = fresh_vsymbol v in
  let m = Mvs.mapi add_vs p.pat_vars in
  let p = pat_rename_all m p in
  Mvs.union (fun _ _ t -> Some t) h (Mvs.map t_var m), p

let t_open_bound (v,b,t) =
  let m,v = vs_rename b.bv_subst v in
  v, t_subst_unsafe m t

let t_open_branch (p,b,t) =
  let m,p = pat_rename b.bv_subst p in
  p, t_subst_unsafe m t

let t_open_quant (vl,b,tl,f) =
  let m,vl = vl_rename b.bv_subst vl in
  let tl = tr_map (t_subst_unsafe m) tl in
  (vl, tl, t_subst_unsafe m f)

(** open bindings with optimized closing callbacks *)

let t_open_bound_cb tb =
  let v, t = t_open_bound tb in
  let close v' t' =
    if t_equal t t' && vs_equal v v' then tb else t_close_bound v' t'
  in
  v, t, close

let t_open_branch_cb tbr =
  let p, t = t_open_branch tbr in
  let close p' t' =
    if t_equal t t' && pat_equal p p' then tbr else t_close_branch p' t'
  in
  p, t, close

let t_open_quant_cb fq =
  let vl, tl, f = t_open_quant fq in
  let close vl' tl' f' =
    if t_equal f f' && tr_equal tl tl' && list_all2 vs_equal vl vl'
    then fq else t_close_quant vl' tl' f'
  in
  vl, tl, f, close

(* constructors with type checking *)

let ls_arg_inst ls tl =
  let mtch s ty t = ty_match s ty (t_type t) in
  try List.fold_left2 mtch Mtv.empty ls.ls_args tl
  with Invalid_argument _ -> raise (BadArity
    (ls, List.length ls.ls_args, List.length tl))

let ls_app_inst ls tl ty =
  let s = ls_arg_inst ls tl in
  match ls.ls_value, ty with
    | Some _, None -> raise (PredicateSymbolExpected ls)
    | None, Some _ -> raise (FunctionSymbolExpected ls)
    | Some vty, Some ty -> ty_match s vty ty
    | None, None -> s

let t_app_infer ls tl =
  let s = ls_arg_inst ls tl in
  t_app ls tl (oty_inst s ls.ls_value)

let t_app ls tl ty = ignore (ls_app_inst ls tl ty); t_app ls tl ty

let fs_app fs tl ty = t_app fs tl (Some ty)
let ps_app ps tl    = t_app ps tl None

let t_const c = match c with
  | ConstInt _  -> t_const c ty_int
  | ConstReal _ -> t_const c ty_real

let t_if f t1 t2 =
  t_ty_check t2 t1.t_ty;
  t_if (t_prop f) t1 t2

let t_let t1 ((v,_,t2) as bt) =
  vs_check v t1;
  t_let t1 bt t2.t_ty

exception EmptyCase

let t_case t bl =
  let tty = t_type t in
  let bty = match bl with
    | (_,_,tbr) :: _ -> tbr.t_ty
    | _ -> raise EmptyCase
  in
  let t_check_branch (p,_,tbr) =
    ty_equal_check tty p.pat_ty;
    t_ty_check tbr bty
  in
  List.iter t_check_branch bl;
  t_case t bl bty

let t_eps ((v,_,f) as bf) =
  ignore (t_prop f);
  t_eps bf (Some v.vs_ty)

let t_quant q ((vl,_,_,f) as qf) =
  if vl = [] then f else t_quant q qf

let t_binary op f1 f2 = t_binary op (t_prop f1) (t_prop f2)
let t_not f = t_not (t_prop f)

let t_forall  = t_quant Tforall
let t_exists  = t_quant Texists
let t_and     = t_binary Tand
let t_or      = t_binary Tor
let t_implies = t_binary Timplies
let t_iff     = t_binary Tiff

let asym_label = "asym_split"
let t_and_asym t1 t2 = t_label [asym_label] (t_and t1 t2)
let t_or_asym  t1 t2 = t_label [asym_label] (t_or  t1 t2)

(* closing constructors *)

let t_quant_close q vl tl f =
  if vl = [] then t_prop f else t_quant q (t_close_quant vl tl f)

let t_forall_close = t_quant_close Tforall
let t_exists_close = t_quant_close Texists

let t_let_close v t1 t2 = t_let t1 (t_close_bound v t2)

let t_eps_close v f = t_eps (t_close_bound v f)

(* built-in symbols *)

let ps_equ =
  let v = ty_var (create_tvsymbol (id_fresh "a")) in
  create_psymbol (id_fresh "infix =") [v; v]

let t_equ t1 t2 = ps_app ps_equ [t1; t2]
let t_neq t1 t2 = t_not (ps_app ps_equ [t1; t2])

let fs_tuple_ids = Hid.create 17

let fs_tuple = Util.memo_int 17 (fun n ->
  let ts = ts_tuple n in
  let tl = List.map ty_var ts.ts_args in
  let ty = ty_app ts tl in
  let fs = create_fsymbol (id_fresh ("Tuple" ^ string_of_int n)) tl ty in
  Hid.add fs_tuple_ids fs.ls_name n;
  fs)

let is_fs_tuple fs = ls_equal fs (fs_tuple (List.length fs.ls_args))

let is_fs_tuple_id id =
  try Some (Hid.find fs_tuple_ids id) with Not_found -> None

let t_tuple tl =
  let ty = ty_tuple (List.map t_type tl) in
  fs_app (fs_tuple (List.length tl)) tl ty

let fs_func_app =
  let ty_a = ty_var (create_tvsymbol (id_fresh "a")) in
  let ty_b = ty_var (create_tvsymbol (id_fresh "b")) in
  create_fsymbol (id_fresh "infix @!") [ty_func ty_a ty_b; ty_a] ty_b

let ps_pred_app =
  let ty_a = ty_var (create_tvsymbol (id_fresh "a")) in
  create_psymbol (id_fresh "infix @?") [ty_pred ty_a; ty_a]

let t_func_app fn t = t_app_infer fs_func_app [fn; t]
let t_pred_app pr t = ps_app ps_pred_app [pr; t]

let t_func_app_l = List.fold_left t_func_app

let t_pred_app_l pr tl = match List.rev tl with
  | t::tl -> t_pred_app (t_func_app_l pr (List.rev tl)) t
  | _ -> Pervasives.invalid_arg "t_pred_app_l"

(** Term library *)

(* generic map over types, symbols and variables *)

let gen_fresh_vsymbol fnT v =
  let ty = fnT v.vs_ty in
  if ty_equal ty v.vs_ty then v else
  create_vsymbol (id_clone v.vs_name) ty

let gen_vs_rename fnT h v =
  let u = gen_fresh_vsymbol fnT v in
  Mvs.add v u h, u

let gen_vl_rename fnT h vl =
  Util.map_fold_left (gen_vs_rename fnT) h vl

let gen_pat_rename fnT fnL h p =
  let add_vs v () = gen_fresh_vsymbol fnT v in
  let m = Mvs.mapi add_vs p.pat_vars in
  let p = pat_gen_map fnT fnL m p in
  Mvs.union (fun _ _ t -> Some t) h m, p

let gen_bnd_rename fnT fnE h b =
  let add_bv v n m = Mvs.add (Mvs.find v h) n m in
  let bvs = Mvs.fold add_bv b.bv_vars Mvs.empty in
  let add_bs v t (nh, m) =
    let nh,v = gen_vs_rename fnT nh v in
    nh, Mvs.add v (fnE t) m
  in
  let h,bsb = Mvs.fold add_bs b.bv_subst (h,Mvs.empty) in
  h, { bv_vars = bvs ; bv_subst = bsb }

let rec t_gen_map fnT fnL m t =
  let fn = t_gen_map fnT fnL m in
  t_label_copy t (match t.t_node with
    | Tvar v ->
        let u = Mvs.find_default v v m in
        ty_equal_check (fnT v.vs_ty) u.vs_ty;
        t_var u
    | Tconst _ ->
        t
    | Tapp (fs, tl) ->
        t_app (fnL fs) (List.map fn tl) (option_map fnT t.t_ty)
    | Tif (f, t1, t2) ->
        t_if (fn f) (fn t1) (fn t2)
    | Tlet (t1, (u,b,t2)) ->
        let m,b = gen_bnd_rename fnT fn m b in
        let m,u = gen_vs_rename fnT m u in
        t_let (fn t1) (u, b, t_gen_map fnT fnL m t2)
    | Tcase (t1, bl) ->
        let fn_br (p,b,t2) =
          let m,b = gen_bnd_rename fnT fn m b in
          let m,p = gen_pat_rename fnT fnL m p in
          (p, b, t_gen_map fnT fnL m t2)
        in
        t_case (fn t1) (List.map fn_br bl)
    | Teps (u,b,f) ->
        let m,b = gen_bnd_rename fnT fn m b in
        let m,u = gen_vs_rename fnT m u in
        t_eps (u, b, t_gen_map fnT fnL m f)
    | Tquant (q, (vl,b,tl,f)) ->
        let m,b = gen_bnd_rename fnT fn m b in
        let m,vl = gen_vl_rename fnT m vl in
        let fn = t_gen_map fnT fnL m in
        t_quant q (vl, b, tr_map fn tl, fn f)
    | Tbinop (op, f1, f2) ->
        t_binary op (fn f1) (fn f2)
    | Tnot f1 ->
        t_not (fn f1)
    | Ttrue | Tfalse ->
        t)

let t_gen_map fnT fnL mapV t = t_gen_map (Wty.memoize 17 fnT) fnL mapV t

(* map over type and logic symbols *)

let gen_mapV fnT = Mvs.mapi (fun v _ -> gen_fresh_vsymbol fnT v)

let t_s_map fnT fnL t = t_gen_map fnT fnL (gen_mapV fnT t.t_vars) t

(* simultaneous substitution into types and terms *)

let t_ty_subst mapT mapV t =
  let fnT = ty_inst mapT in
  let m = gen_mapV fnT t.t_vars in
  let t = t_gen_map fnT (fun ls -> ls) m t in
  let add _ v t m = vs_check v t; Mvs.add v t m in
  let m = Mvs.fold2_inter add m mapV Mvs.empty in
  t_subst_unsafe m t

(* fold over symbols *)

let rec t_gen_fold fnT fnL acc t =
  let fn = t_gen_fold fnT fnL in
  let acc = option_fold fnT acc t.t_ty in
  match t.t_node with
  | Tconst _ | Tvar _ -> acc
  | Tapp (f, tl) -> List.fold_left fn (fnL acc f) tl
  | Tif (f, t1, t2) -> fn (fn (fn acc f) t1) t2
  | Tlet (t1, (_,b,t2)) -> fn (bnd_fold fn (fn acc t1) b) t2
  | Tcase (t1, bl) ->
      let branch acc (p,b,t) =
        fn (pat_gen_fold fnT fnL (bnd_fold fn acc b) p) t in
      List.fold_left branch (fn acc t1) bl
  | Teps (_,b,f) -> fn (bnd_fold fn acc b) f
  | Tquant (_, (vl,b,tl,f1)) ->
      (* these variables (and their types) may never appear below *)
      let acc = List.fold_left (fun a v -> fnT a v.vs_ty) acc vl in
      fn (tr_fold fn (bnd_fold fn acc b) tl) f1
  | Tbinop (_, f1, f2) -> fn (fn acc f1) f2
  | Tnot f1 -> fn acc f1
  | Ttrue | Tfalse -> acc

let t_s_fold = t_gen_fold

let t_s_all prT prL t =
  try t_s_fold (all_fn prT) (all_fn prL) true t with FoldSkip -> false

let t_s_any prT prL t =
  try t_s_fold (any_fn prT) (any_fn prL) false t with FoldSkip -> true

(* map/fold over types in terms and formulas *)

let t_ty_map fn t = t_s_map fn (fun ls -> ls) t

let t_ty_fold fn acc t = t_s_fold fn Util.const acc t

let t_ty_freevars = t_ty_fold ty_freevars

(* map/fold over applications in terms and formulas (but not in patterns!) *)

let rec t_app_map fn t =
  let t = t_map_unsafe (t_app_map fn) t in
  match t.t_node with
    | Tapp (ls,tl) ->
        let ls = fn ls (List.map t_type tl) t.t_ty in
        t_label_copy t (t_app ls tl t.t_ty)
    | _ -> t

let rec t_app_fold fn acc t =
  let acc = t_fold_unsafe (t_app_fold fn) acc t in
  match t.t_node with
    | Tapp (ls,tl) -> fn acc ls (List.map t_type tl) t.t_ty
    | _ -> acc

(* Type- and binding-safe traversal *)

let t_map fn t = match t.t_node with
  | Tlet (t1, b) ->
      let u,t2,close = t_open_bound_cb b in
      t_label_copy t (t_let (fn t1) (close u (fn t2)))
  | Tcase (t1, bl) ->
      let brn b = let p,t,close = t_open_branch_cb b in close p (fn t) in
      t_label_copy t (t_case (fn t1) (List.map brn bl))
  | Teps b ->
      let u,t1,close = t_open_bound_cb b in
      t_label_copy t (t_eps (close u (fn t1)))
  | Tquant (q, b) ->
      let vl,tl,f1,close = t_open_quant_cb b in
      t_label_copy t (t_quant q (close vl (tr_map fn tl) (fn f1)))
  | _ ->
      t_map_unsafe fn t

let t_map fn = t_map (fun t ->
  let res = fn t in t_ty_check res t.t_ty; res)

(* safe opening fold *)

let t_fold fn acc t = match t.t_node with
  | Tlet (t1, b) ->
      let _,t2 = t_open_bound b in fn (fn acc t1) t2
  | Tcase (t1, bl) ->
      let brn acc b = let _,t = t_open_branch b in fn acc t in
      List.fold_left brn (fn acc t1) bl
  | Teps b ->
      let _,f = t_open_bound b in fn acc f
  | Tquant (_, b) ->
      let _, tl, f1 = t_open_quant b in tr_fold fn (fn acc f1) tl
  | _ -> t_fold_unsafe fn acc t

let t_all pr t = try t_fold (all_fn pr) true t with FoldSkip -> false
let t_any pr t = try t_fold (any_fn pr) false t with FoldSkip -> true

(* safe opening map_fold *)

let t_map_fold fn acc t = match t.t_node with
  | Tlet (e,b) ->
      let acc, e = fn acc e in
      let u,t1,close = t_open_bound_cb b in
      let acc, t1 = fn acc t1 in
      acc, t_label_copy t (t_let e (close u t1))
  | Tcase (e,bl) ->
      let acc, e = fn acc e in
      let brn acc b =
        let p,t,close = t_open_branch_cb b in
        let acc,t = fn acc t in acc, close p t in
      let acc, bl = map_fold_left brn acc bl in
      acc, t_label_copy t (t_case e bl)
  | Teps b ->
      let u,t1,close = t_open_bound_cb b in
      let acc, t1 = fn acc t1 in
      acc, t_label_copy t (t_eps (close u t1))
  | Tquant (q,b) ->
      let vl,tl,f1,close = t_open_quant_cb b in
      let acc, tl = tr_map_fold fn acc tl in
      let acc, f1 = fn acc f1 in
      acc, t_label_copy t (t_quant q (close vl tl f1))
  | _ -> t_map_fold_unsafe fn acc t

let t_map_fold fn = t_map_fold (fun acc t ->
  let res = fn acc t in t_ty_check (snd res) t.t_ty; res)

(* polarity map *)

let t_map_sign fn sign f = t_label_copy f (match f.t_node with
  | Tbinop (Timplies, f1, f2) ->
      t_implies (fn (not sign) f1) (fn sign f2)
  | Tbinop (Tiff, f1, f2) ->
      let f1p = fn sign f1 in let f1n = fn (not sign) f1 in
      let f2p = fn sign f2 in let f2n = fn (not sign) f2 in
      if t_equal f1p f1n && t_equal f2p f2n then t_iff f1p f2p
      else if sign
        then t_and (t_implies f1n f2p) (t_implies f2n f1p)
        else t_implies (t_or f1n f2n) (t_and f1p f2p)
  | Tnot f1 ->
      t_not (fn (not sign) f1)
  | Tif (f1, f2, f3) when f.t_ty = None ->
      let f1p = fn sign f1 in let f1n = fn (not sign) f1 in
      let f2 = fn sign f2 in let f3 = fn sign f3 in
      if t_equal f1p f1n then t_if f1p f2 f3 else if sign
        then t_and (t_implies f1n f2) (t_implies (t_not f1p) f3)
        else t_or (t_and f1p f2) (t_and (t_not f1n) f3)
  | Tif _
  | Teps _ -> failwith "t_map_sign: cannot determine polarity"
  | _ -> t_map (fn sign) f)

(* continuation-passing traversal *)

let rec list_map_cont fnL contL = function
  | e::el ->
      let cont_l e el = contL (e::el) in
      let cont_e e = list_map_cont fnL (cont_l e) el in
      fnL cont_e e
  | [] ->
      contL []

let t_map_cont fn contT t =
  let contT e = contT (t_label_copy t e) in
  match t.t_node with
  | Tvar _ | Tconst _ -> contT t
  | Tapp (fs, tl) ->
      let cont_app tl = contT (t_app fs tl t.t_ty) in
      list_map_cont fn cont_app tl
  | Tif (f, t1, t2) ->
      let cont_else f t1 t2 = contT (t_if f t1 t2) in
      let cont_then f t1 = fn (cont_else f t1) t2 in
      let cont_if f = fn (cont_then f) t1 in
      fn cont_if f
  | Tlet (t1, b) ->
      let u,t2,close = t_open_bound_cb b in
      let cont_in t1 t2 = contT (t_let t1 (close u t2)) in
      let cont_let t1 = fn (cont_in t1) t2 in
      fn cont_let t1
  | Tcase (t1, bl) ->
      let fnB contB b =
        let pat,t,close = t_open_branch_cb b in
        fn (fun t -> contB (close pat t)) t
      in
      let cont_with t1 bl = contT (t_case t1 bl) in
      let cont_case t1 = list_map_cont fnB (cont_with t1) bl in
      fn cont_case t1
  | Teps b ->
      let u,f,close = t_open_bound_cb b in
      let cont_eps f = contT (t_eps (close u f)) in
      fn cont_eps f
  | Tquant (q, b) ->
      let vl, tl, f1, close = t_open_quant_cb b in
      let cont_dot tl f1 = contT (t_quant q (close vl tl f1)) in
      let cont_quant tl = fn (cont_dot tl) f1 in
      list_map_cont (list_map_cont fn) cont_quant tl
  | Tbinop (op, f1, f2) ->
      let cont_r f1 f2 = contT (t_binary op f1 f2) in
      let cont_l f1 = fn (cont_r f1) f2 in
      fn cont_l f1
  | Tnot f1 ->
      let cont_not f1 = contT (t_not f1) in
      fn cont_not f1
  | Ttrue | Tfalse -> contT t

let t_map_cont fn = t_map_cont (fun cont t ->
  fn (fun e -> t_ty_check e t.t_ty; cont e) t)

(* map/fold over free variables *)

let t_v_map fn t =
  let fn v _ = let res = fn v in vs_check v res; res in
  t_subst_unsafe (Mvs.mapi fn t.t_vars) t

let t_v_fold fn acc t = Mvs.fold (fun v _ a -> fn a v) t.t_vars acc

let t_v_all pr t = Mvs.for_all (fun v _ -> pr v) t.t_vars
let t_v_any pr t = Mvs.exists  (fun v _ -> pr v) t.t_vars

(* replaces variables with terms in term [t] using map [m] *)

let t_subst m t = Mvs.iter vs_check m; t_subst_unsafe m t

let t_subst_single v t1 t = t_subst (Mvs.singleton v t1) t

(* set of free variables *)

let t_freevars = add_t_vars

(* alpha-equality *)

let vs_rename_alpha c h vs = incr c; Mvs.add vs !c h

let vl_rename_alpha c h vl = List.fold_left (vs_rename_alpha c) h vl

let rec pat_rename_alpha c h p = match p.pat_node with
  | Pvar v -> vs_rename_alpha c h v
  | Pas (p, v) -> pat_rename_alpha c (vs_rename_alpha c h v) p
  | Por (p, _) -> pat_rename_alpha c h p
  | _ -> pat_fold (pat_rename_alpha c) h p

let rec pat_equal_alpha p1 p2 =
  pat_equal p1 p2 ||
  ty_equal p1.pat_ty p2.pat_ty &&
  match p1.pat_node, p2.pat_node with
  | Pwild, Pwild | Pvar _, Pvar _ -> true
  | Papp (f1, l1), Papp (f2, l2) ->
      ls_equal f1 f2 && List.for_all2 pat_equal_alpha l1 l2
  | Pas (p1, _), Pas (p2, _) -> pat_equal_alpha p1 p2
  | Por (p1, q1), Por (p2, q2) ->
      pat_equal_alpha p1 p2 && pat_equal_alpha q1 q2
  | _ -> false

let rec t_equal_alpha c1 c2 m1 m2 t1 t2 =
  t_equal t1 t2 || oty_equal t1.t_ty t2.t_ty &&
  let t_eq = t_equal_alpha c1 c2 m1 m2 in
  match t1.t_node, t2.t_node with
    | Tvar v1, Tvar v2 when Mvs.mem v1 m1 ->
        Mvs.mem v2 m2 && Mvs.find v1 m1 = Mvs.find v2 m2
    | Tvar v1, Tvar v2 when not (Mvs.mem v2 m2) ->
        vs_equal v1 v2
    | Tconst c1, Tconst c2 ->
        c1 = c2
    | Tapp (s1,l1), Tapp (s2,l2) ->
        ls_equal s1 s2 && List.for_all2 t_eq l1 l2
    | Tif (f1,t1,e1), Tif (f2,t2,e2) ->
        t_eq f1 f2 && t_eq t1 t2 && t_eq e1 e2
    | Tlet (t1,b1), Tlet (t2,b2) ->
        t_eq t1 t2 &&
        let u1,e1 = t_open_bound b1 in
        let u2,e2 = t_open_bound b2 in
        let m1 = vs_rename_alpha c1 m1 u1 in
        let m2 = vs_rename_alpha c2 m2 u2 in
        t_equal_alpha c1 c2 m1 m2 e1 e2
    | Tcase (t1,bl1), Tcase (t2,bl2) ->
        t_eq t1 t2 &&
        let br_eq ((p1,_,_) as b1) ((p2,_,_) as b2) =
          pat_equal_alpha p1 p2 &&
          let p1,e1 = t_open_branch b1 in
          let p2,e2 = t_open_branch b2 in
          let m1 = pat_rename_alpha c1 m1 p1 in
          let m2 = pat_rename_alpha c2 m2 p2 in
          t_equal_alpha c1 c2 m1 m2 e1 e2
        in
        list_all2 br_eq bl1 bl2
    | Teps b1, Teps b2 ->
        let u1,e1 = t_open_bound b1 in
        let u2,e2 = t_open_bound b2 in
        let m1 = vs_rename_alpha c1 m1 u1 in
        let m2 = vs_rename_alpha c2 m2 u2 in
        t_equal_alpha c1 c2 m1 m2 e1 e2
    | Tquant (q1,((vl1,_,_,_) as b1)), Tquant (q2,((vl2,_,_,_) as b2)) ->
        q1 = q2 &&
        list_all2 (fun v1 v2 -> ty_equal v1.vs_ty v2.vs_ty) vl1 vl2 &&
        let vl1,_,e1 = t_open_quant b1 in
        let vl2,_,e2 = t_open_quant b2 in
        let m1 = vl_rename_alpha c1 m1 vl1 in
        let m2 = vl_rename_alpha c2 m2 vl2 in
        t_equal_alpha c1 c2 m1 m2 e1 e2
    | Tbinop (a,f1,g1), Tbinop (b,f2,g2) ->
        a = b && t_eq f1 f2 && t_eq g1 g2
    | Tnot f1, Tnot f2 ->
        t_eq f1 f2
    | Ttrue, Ttrue | Tfalse, Tfalse ->
        true
    | _ -> false

let t_equal_alpha = t_equal_alpha (ref (-1)) (ref (-1)) Mvs.empty Mvs.empty

(* hash modulo alpha *)

let rec pat_hash_alpha p =
  match p.pat_node with
  | Pwild -> 0
  | Pvar _ -> 1
  | Papp (f, l) ->
      let acc = Hashcons.combine 2 (ls_hash f) in
      Hashcons.combine_list pat_hash_alpha acc l
  | Pas (p, _) -> Hashcons.combine 3 (pat_hash_alpha p)
  | Por (p, q) ->
      Hashcons.combine
        (Hashcons.combine 4 (pat_hash_alpha p)) (pat_hash_alpha q)

let rec t_hash_alpha c m t =
  let fn = t_hash_alpha c m in
  match t.t_node with
  | Tvar v ->
      Hashcons.combine 0 (Mvs.find_default v (vs_hash v) m)
  | Tconst c ->
      Hashcons.combine 1 (Hashtbl.hash c)
  | Tapp (s,l) ->
      let acc = Hashcons.combine 2 (ls_hash s) in
      Hashcons.combine_list fn acc l
  | Tif (f,t1,t2) ->
      Hashcons.combine3 3 (fn f) (fn t1) (fn t2)
  | Tlet (t1,b) ->
      let u,t2 = t_open_bound b in
      let m = vs_rename_alpha c m u in
      Hashcons.combine2 4 (fn t1) (t_hash_alpha c m t2)
  | Tcase (t1,bl) ->
      let hash_br b =
        let p,t2 = t_open_branch b in
        let m = pat_rename_alpha c m p in
        t_hash_alpha c m t2
      in
      let acc = Hashcons.combine 5 (fn t1) in
      Hashcons.combine_list hash_br acc bl
  | Teps b ->
      let u,f = t_open_bound b in
      let m = vs_rename_alpha c m u in
      Hashcons.combine 6 (t_hash_alpha c m f)
  | Tquant (q,b) ->
      let vl,_,f1 = t_open_quant b in
      let m = vl_rename_alpha c m vl in
      let hq = match q with Tforall -> 1 | Texists -> 2 in
      Hashcons.combine2 1 hq (t_hash_alpha c m f1)
  | Tbinop (o,f,g) ->
      let ho = match o with
        | Tand -> 3 | Tor -> 4 | Timplies -> 5 | Tiff -> 7
      in
      Hashcons.combine3 2 ho (fn f) (fn g)
  | Tnot f ->
      Hashcons.combine 3 (fn f)
  | Ttrue -> 4
  | Tfalse -> 5

let t_hash_alpha = t_hash_alpha (ref (-1)) Mvs.empty

module Hterm_alpha = Hashtbl.Make (struct
  type t = term
  let equal = t_equal_alpha
  let hash = t_hash_alpha
end)

(* binder-free term/formula matching *)

(* exception NoMatch *)

(* let rec t_match s t1 t2 = *)
(*   if not (oty_equal t1.t_ty t2.t_ty) then raise NoMatch else *)
(*   match t1.t_node, t2.t_node with *)
(*     | Tconst c1, Tconst c2 when c1 = c2 -> s *)
(*     | Tvar v1, _ -> *)
(*         Mvs.change v1 (function *)
(*           | None -> Some t2 *)
(*           | Some t1 as r when t_equal t1 t2 -> r *)
(*           | _ -> raise NoMatch) s *)
(*     | Tapp (s1,l1), Tapp (s2,l2) when ls_equal s1 s2 -> *)
(*         List.fold_left2 t_match s l1 l2 *)
(*     | Tif (f1,t1,e1), Tif (f2,t2,e2) -> *)
(*         t_match (t_match (t_match s f1 f2) t1 t2) e1 e2 *)
(*     | Tbinop (op1,f1,g1), Tbinop (op2,f2,g2) when op1 = op2 -> *)
(*         t_match (t_match s f1 f2) g1 g2 *)
(*     | Tnot f1, Tnot f2 -> *)
(*         t_match s f1 f2 *)
(*     | Ttrue, Ttrue *)
(*     | Tfalse, Tfalse -> *)
(*         s *)
(*     | _ -> raise NoMatch *)

(* occurrence check *)

let rec t_occurs r t =
  t_equal r t || t_any (t_occurs r) t

let rec t_occurs_alpha r t =
  t_equal_alpha r t || t_any (t_occurs_alpha r) t

(* substitutes term [t2] for term [t1] in term [t] *)

let rec t_replace t1 t2 t =
  if t_equal t t1 then t2 else t_map (t_replace t1 t2) t

let t_replace t1 t2 t =
  t_ty_check t2 t1.t_ty;
  t_replace t1 t2 t

let rec t_replace_alpha t1 t2 t =
  if t_equal_alpha t t1 then t2 else t_map (t_replace_alpha t1 t2) t

let t_replace_alpha t1 t2 t =
  t_ty_check t2 t1.t_ty;
  t_replace_alpha t1 t2 t

(* constructors with propositional simplification *)

let t_not_simp f = match f.t_node with
  | Ttrue  -> t_false
  | Tfalse -> t_true
  | Tnot f -> f
  | _      -> t_not f

let t_and_simp f1 f2 = match f1.t_node, f2.t_node with
  | Ttrue, _  -> f2
  | _, Ttrue  -> f1
  | Tfalse, _ -> f1
  | _, Tfalse -> f2
  | _, _      -> if t_equal f1 f2 then f1 else t_and f1 f2

let t_and_simp_l l = List.fold_left t_and_simp t_true l

let t_or_simp f1 f2 = match f1.t_node, f2.t_node with
  | Ttrue, _  -> f1
  | _, Ttrue  -> f2
  | Tfalse, _ -> f2
  | _, Tfalse -> f1
  | _, _      -> if t_equal f1 f2 then f1 else t_or f1 f2

let t_or_simp_l l = List.fold_left t_or_simp t_false l

let t_and_asym_simp f1 f2 = match f1.t_node, f2.t_node with
  | Ttrue, _  -> f2
  | _, Ttrue  -> f1
  | Tfalse, _ -> f1
  | _, Tfalse -> f2
  | _, _      -> if t_equal f1 f2 then f1 else t_and_asym f1 f2

let t_and_asym_simp_l l = List.fold_left t_and_asym_simp t_true l

let t_or_asym_simp f1 f2 = match f1.t_node, f2.t_node with
  | Ttrue, _  -> f1
  | _, Ttrue  -> f2
  | Tfalse, _ -> f2
  | _, Tfalse -> f1
  | _, _      -> if t_equal f1 f2 then f1 else t_or_asym f1 f2

let t_or_asym_simp_l l = List.fold_left t_or_asym_simp t_false l

let t_implies_simp f1 f2 = match f1.t_node, f2.t_node with
  | Ttrue, _  -> f2
  | _, Ttrue  -> f2
  | Tfalse, _ -> t_true
  | _, Tfalse -> t_not_simp f1
  | _, _      -> if t_equal f1 f2 then t_true else t_implies f1 f2

let t_iff_simp f1 f2 = match f1.t_node, f2.t_node with
  | Ttrue, _  -> f2
  | _, Ttrue  -> f1
  | Tfalse, _ -> t_not_simp f2
  | _, Tfalse -> t_not_simp f1
  | _, _      -> if t_equal f1 f2 then t_true else t_iff f1 f2

let t_binary_simp op = match op with
  | Tand     -> t_and_simp
  | Tor      -> t_or_simp
  | Timplies -> t_implies_simp
  | Tiff     -> t_iff_simp

let t_if_simp f1 f2 f3 = match f1.t_node, f2.t_node, f3.t_node with
  | Ttrue, _, _  -> f2
  | Tfalse, _, _ -> f3
  | _, Ttrue, _  -> t_implies_simp (t_not_simp f1) f3
  | _, Tfalse, _ -> t_and_simp (t_not_simp f1) f3
  | _, _, Ttrue  -> t_implies_simp f1 f2
  | _, _, Tfalse -> t_and_simp f1 f2
  | _, _, _      -> if t_equal f2 f3 then f2 else t_if f1 f2 f3

let small t = match t.t_node with
  | Tvar _ | Tconst _ -> true
  | _ -> false

let t_let_simp e ((v,b,t) as bt) =
  let n = Mvs.find_default v 0 t.t_vars in
  if n = 0 then
    t_subst_unsafe b.bv_subst t else
  if n = 1 || small e then begin
    vs_check v e;
    t_subst_unsafe (Mvs.add v e b.bv_subst) t
  end else
    t_let e bt

let t_let_close_simp v e t =
  let n = Mvs.find_default v 0 t.t_vars in
  if n = 0 then t else
  if n = 1 || small e then
    t_subst_single v e t
  else
    t_let_close v e t

let v_occurs f v = Mvs.mem v f.t_vars
let v_subset f e = Mvs.set_submap e.t_vars f.t_vars

let vl_filter f vl = List.filter (v_occurs f) vl
let tr_filter f tl = List.filter (List.for_all (v_subset f)) tl

let t_quant_simp q ((vl,_,_,f) as qf) =
  if List.for_all (v_occurs f) vl then
    t_quant q qf
  else
    let vl,tl,f = t_open_quant qf in
    let vl = vl_filter f vl in if vl = [] then f else
    t_quant_close q vl (tr_filter f tl) f

let t_quant_close_simp q vl tl f =
  if List.for_all (v_occurs f) vl then
    t_quant_close q vl tl f
  else
    let vl = vl_filter f vl in if vl = [] then f else
    t_quant_close q vl (tr_filter f tl) f

let t_forall_simp = t_quant_simp Tforall
let t_exists_simp = t_quant_simp Texists

let t_forall_close_simp = t_quant_close_simp Tforall
let t_exists_close_simp = t_quant_close_simp Texists

let t_equ_simp t1 t2 = if t_equal t1 t2 then t_true  else t_equ t1 t2
let t_neq_simp t1 t2 = if t_equal t1 t2 then t_false else t_neq t1 t2

let t_forall_close_merge vs f =
  match f.t_node with
  | Tquant (Tforall, fq) ->
      let vs', trs, f = t_open_quant fq in
      t_forall_close (vs@vs') trs f
  | _ -> t_forall_close vs [] f

let t_map_simp fn f = t_label_copy f (match f.t_node with
  | Tapp (p, [t1;t2]) when ls_equal p ps_equ ->
      t_equ_simp (fn t1) (fn t2)
  | Tif (f1, f2, f3) ->
      t_if_simp (fn f1) (fn f2) (fn f3)
  | Tlet (t, b) ->
      let u,t2,close = t_open_bound_cb b in
      t_let_simp (fn t) (close u (fn t2))
  | Tquant (q, b) ->
      let vl,tl,f1,close = t_open_quant_cb b in
      t_quant_simp q (close vl (tr_map fn tl) (fn f1))
  | Tbinop (op, f1, f2) ->
      t_binary_simp op (fn f1) (fn f2)
  | Tnot f1 ->
      t_not_simp (fn f1)
  | _ -> t_map fn f)

let t_map_simp fn = t_map_simp (fun t ->
  let res = fn t in t_ty_check res t.t_ty; res)

(** Traversal with separate functions for value-typed and prop-typed terms *)

module TermTF = struct
  let t_select fnT fnF e =
    if e.t_ty = None then fnF e else fnT e

  let t_selecti fnT fnF acc e =
    if e.t_ty = None then fnF acc e else fnT acc e

  let t_map fnT fnF = t_map (t_select fnT fnF)
  let t_fold fnT fnF = t_fold (t_selecti fnT fnF)
  let t_map_fold fnT fnF = t_map_fold (t_selecti fnT fnF)
  let t_all prT prF = t_all (t_select prT prF)
  let t_any prT prF = t_any (t_select prT prF)
  let t_map_simp fnT fnF = t_map_simp (t_select fnT fnF)
  let t_map_sign fnT fnF = t_map_sign (t_selecti fnT fnF)
  let t_map_cont fnT fnF = t_map_cont (t_selecti fnT fnF)
  let tr_map fnT fnF = tr_map (t_select fnT fnF)
  let tr_fold fnT fnF = tr_fold (t_selecti fnT fnF)
  let tr_map_fold fnT fnF = tr_map_fold (t_selecti fnT fnF)
end

