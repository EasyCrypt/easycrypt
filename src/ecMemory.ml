(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcSymbols
open EcUtils
open EcTypes

module Msym = EcSymbols.Msym

(* -------------------------------------------------------------------- *)
type memory = EcIdent.t

let mem_equal = EcIdent.id_equal

(* -------------------------------------------------------------------- *)
type proj_arg =
  { arg_ty : EcTypes.ty; (* type of the procedure argument "arg" *)
    arg_pos : int;       (* projection *)
    arg_len : int;       (* number of arguments *)
  }

(* The [EcIdent.t] is the ident corresponding to the symbol in local memory *)
type local_memtype = {
  mt_vars : (proj_arg option * ty * EcIdent.t) Msym.t
}

type memtype = local_memtype option

let mt_fv = function
  | None -> EcIdent.Mid.empty
  | Some lmt ->
    let fv = EcIdent.Mid.empty in
    Msym.fold (fun _ (_,ty,_) fv -> EcIdent.fv_union fv ty.ty_fv) lmt.mt_vars fv

let lmt_equal mt1 mt2 =
  Msym.equal (fun (p1,ty1,id1) (p2,ty2,id2) ->
      p1 = p2 && ty_equal ty1 ty2 && EcIdent.id_equal id1 id2)
    mt1.mt_vars mt2.mt_vars

let lmt_bindings mt = mt.mt_vars

let mt_equal mt1 mt2 =
  match mt1, mt2 with
  | Some mt1, Some mt2 -> lmt_equal mt1 mt2
  | None, None         -> true
  | _   , _            -> false

let mt_bindings = function
  | None -> assert false
  | Some mt -> lmt_bindings mt

(* -------------------------------------------------------------------- *)
type memenv = memory * memtype

let me_equal (m1,mt1) (m2,mt2) =
  mem_equal m1 m2 && mt_equal mt1 mt2

(* -------------------------------------------------------------------- *)
let memory   (m,_) = m
let memtype  (_,mt) = mt
let bindings (_,mt) = mt_bindings mt

(* -------------------------------------------------------------------- *)
exception DuplicatedMemoryBinding of symbol

(* -------------------------------------------------------------------- *)
let empty_local (me : memory) =
  (me, Some { mt_vars   = Msym.empty; } )

let abstract (me:memory) = (me,None)

(* -------------------------------------------------------------------- *)
let bindp pr (ty : EcTypes.ty) (id : EcIdent.t) ((m,mt) : memenv) =
  let mt = match mt with
    | None -> assert false
    | Some mt -> mt in
  let x = id.id_symb in
  let merger = function
    | Some _ -> raise (DuplicatedMemoryBinding x)
    | None   -> Some (pr,ty,id)
  in
    (m, Some { mt_vars = Msym.change merger x mt.mt_vars })

let bind_proj arg_ty i n ty x me =
  let arg = { arg_ty; arg_pos = i; arg_len = n } in
  bindp (Some arg) ty x me

let bindp_new (x : symbol) pr (ty : EcTypes.ty) (memenv : memenv) =
  let id = EcIdent.create x in
  bindp pr ty id (memenv), id

let bind_proj_new arg_ty i n x ty me =
  let arg = { arg_ty; arg_pos = i; arg_len = n } in
  bindp_new x (Some arg) ty me

let bind_new x ty me = bindp_new x None ty me

(* -------------------------------------------------------------------- *)
let lookup (x : symbol) ((_,mt) : memenv) =
  match mt with
  | None -> None
  | Some mt ->  Msym.find_opt x (lmt_bindings mt)

let is_bound x me = lookup x me <> None

let is_bound_pv pv me = match pv with
  | PVglob _ -> false
  | PVloc id -> is_bound (EcIdent.name id) me

(* -------------------------------------------------------------------- *)

let proj_arg_subst st = function
  | None -> None
  | Some a -> Some ({a with arg_ty = st a.arg_ty })

let mt_subst st o =
  match o with
  | None -> o
  | Some mt ->
    let vars' =
      if st == identity then mt.mt_vars else
        Msym.map (fun (p,ty,id) -> proj_arg_subst st p, st ty, id) mt.mt_vars in
           (* FIXME could be greate to use smart_map *)
    if vars' == mt.mt_vars then o else
      Some { mt_vars   = vars' }

let mt_substm st o =
  mt_subst st o

let me_subst sm st (m,mt as me) =
  let m' = EcIdent.Mid.find_def m m sm in
  let mt' = mt_subst st mt in
  if m' == m && mt' == mt then me else
    (m', mt')

let me_substm sm st me =
  me_subst sm st me
