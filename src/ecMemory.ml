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
  { arg_ty  : ty; (* type of the procedure argument "arg" *)
    arg_pos : int;       (* projection *)
  }

type local_memtype = {
    mt_name : symbol option;      (* provides access to the full local memory *)
    mt_decl : variable list;
    mt_proj : (int * ty) Msym.t;  (* where to find the symbol in mt_decl and its type *)
    mt_ty   : ty;                 (* ttuple (List.map v_type mt_decl) *)
    mt_n    : int;                (* List.length mt_decl *)
  }

let mk_lmt mt_name mt_decl mt_proj =
  { mt_name;
    mt_decl;
    mt_proj;
    mt_ty = ttuple (List.map v_type mt_decl);
    mt_n  = List.length mt_decl;
  }

type memtype = local_memtype option

let mt_fv = function
  | None -> EcIdent.Mid.empty
  | Some lmt ->
    List.fold_left (fun fv v -> EcIdent.fv_union fv v.v_type.ty_fv) EcIdent.Mid.empty lmt.mt_decl

let lmt_equal ty_equal mt1 mt2 =
  mt1.mt_name = mt2.mt_name &&
    List.all2 (fun v1 v2 -> v1.v_name = v2.v_name && ty_equal v1.v_type v2.v_type)
      mt1.mt_decl mt2.mt_decl

let mt_equal_gen ty_equal mt1 mt2 = oeq (lmt_equal ty_equal) mt1 mt2

let mt_equal = mt_equal_gen ty_equal

let mt_iter_ty f mt =
  oiter (fun lmt -> List.iter (fun v -> f v.v_type) lmt.mt_decl) mt

(* -------------------------------------------------------------------- *)
type memenv = memory * memtype

let me_equal_gen ty_equal (m1,mt1) (m2,mt2) =
  mem_equal m1 m2 && mt_equal_gen ty_equal mt1 mt2

let me_equal = me_equal_gen ty_equal

(* -------------------------------------------------------------------- *)
let memory   (m,_) = m
let memtype  (_,mt) = mt

(* -------------------------------------------------------------------- *)
exception DuplicatedMemoryBinding of symbol

(* -------------------------------------------------------------------- *)
let empty_local ~witharg (me : memory) =
  (me, Some (mk_lmt (if witharg then Some arg_symbol else None) [] Msym.empty))

let abstract_mt = None
let abstract (me:memory) = me, abstract_mt

(* -------------------------------------------------------------------- *)

let is_bound_lmt x lmt =
  Some x = lmt.mt_name || Msym.mem x lmt.mt_proj

let is_bound x mt =
  match mt with
  | None -> false
  | Some lmt -> is_bound_lmt x lmt

let lookup (x : symbol) (mt : memtype) : (variable * proj_arg option * int option) option =
  match mt with
  | None -> None
  | Some lmt ->
    if lmt.mt_name = Some x then
      Some ({v_name = x; v_type = lmt.mt_ty}, None, None)
    else
      match Msym.find_opt x lmt.mt_proj with
      | Some (i,xty) ->
        if lmt.mt_n = 1 then
          Some ({ v_name = odfl x lmt.mt_name; v_type = xty}, None, None)
        else
          let v = { v_name = x; v_type = xty } in
          let pa =
            if lmt.mt_name = None then None
            else Some { arg_ty = lmt.mt_ty; arg_pos = i; } in
          Some(v, pa, Some i)
      | None -> None

let lookup_me x me = lookup x (snd me)

let is_bound_pv pv me = match pv with
  | PVglob _ -> false
  | PVloc id -> is_bound id me

(* -------------------------------------------------------------------- *)

let bindall_lmt (vs:variable list) lmt =
  let n = List.length lmt.mt_decl in
  let add_proj mt_proj i v =
    let x = v.v_name in
    if lmt.mt_name = Some x then raise (DuplicatedMemoryBinding x);
    if x = "_" then mt_proj
    else
      let merger = function
        | Some _ -> raise (DuplicatedMemoryBinding x)
        | None   -> Some (n + i,v.v_type) in
    Msym.change merger x mt_proj in
  let mt_decl = lmt.mt_decl @ vs in
  let mt_proj = List.fold_lefti add_proj lmt.mt_proj vs in
  mk_lmt lmt.mt_name mt_decl mt_proj

let bindall (vs:variable list) ((m,mt) : memenv) =
  match mt with
  | None -> assert false
  | Some lmt -> m, Some (bindall_lmt vs lmt)

let bindall_fresh (vs:variable list) ((m,mt) : memenv) =
  match mt with
  | None -> assert false
  | Some lmt ->
    let is_bound x m = Some x = lmt.mt_name || Msym.mem x m in
    let fresh_pv m v =
      let name = v.v_name in
      if name = "_" then m, v
      else
        let name =
          if not(is_bound name m) then name
          else
            let rec for_idx idx =
              let x = Printf.sprintf "%s%d" name idx in
              if is_bound x m then for_idx (idx+1)
              else x in
            for_idx 0 in
        Msym.add name (-1,v.v_type) m, {v with v_name = name } in
    let _, vs = List.map_fold fresh_pv lmt.mt_proj vs in
    let lmt = bindall_lmt vs lmt in
    (m,Some lmt), vs

let bind_fresh v me =
  let me, vs = bindall_fresh [v] me in
  me, as_seq1 vs

(* -------------------------------------------------------------------- *)

let mt_subst st o =
  match o with
  | None -> o
  | Some mt ->
    let decl = mt.mt_decl in
    let decl' =
      if st == identity then decl
      else
        List.Smart.map (fun vty ->
            let ty' = st vty.v_type in
            if ty_equal vty.v_type ty' then vty else {vty with v_type = ty'}) decl in
    if decl == decl' then o
    else
      Some (mk_lmt mt.mt_name decl' (Msym.map (fun (i,ty) -> i, st ty) mt.mt_proj))

let me_subst sm st (m,mt as me) =
  let m' = EcIdent.Mid.find_def m m sm in
  let mt' = mt_subst st mt in
  if m' == m && mt' == mt then me else
    (m', mt')

(* -------------------------------------------------------------------- *)

let for_printing mt =
  match mt with
  | None -> None
  | Some mt -> Some (mt.mt_name, mt.mt_decl)

let get_name s p (_,mt) =
  match mt with
  | None -> None
  | Some mt ->
    match p with
    | None ->
      if Some s = mt.mt_name then
        match mt.mt_decl with
        | [v] when v.v_name <> "_" -> Some v.v_name
        | _ -> Some s
      else
        begin match Msym.find_opt s mt.mt_proj with
        | Some _ -> Some s
        | None   -> None
        end
    | Some i ->
      if Some s = mt.mt_name then
        omap fst (List.find_opt (fun (_,(i',_)) -> i = i') (Msym.bindings mt.mt_proj))
      else
        None

(* -------------------------------------------------------------------- *)

let local_type mt =
  match mt with
  | None -> None
  | Some mt -> Some (ttuple (List.map v_type mt.mt_decl))

let has_locals mt = mt <> None
