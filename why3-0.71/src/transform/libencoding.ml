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
open Term
open Decl
open Theory

let debug = Debug.register_flag "encoding"

(* meta to tag the protected types *)
let meta_kept = register_meta "encoding : kept" [MTty]

(* sort symbol of the "universal" type *)
let ts_base = create_tysymbol (id_fresh "uni") [] None

(* "universal" sort *)
let ty_base = ty_app ts_base []

(* ts_base declaration *)
let d_ts_base = create_ty_decl [ts_base, Tabstract]

(* sort symbol of (polymorphic) types *)
let ts_type = create_tysymbol (id_fresh "ty") [] None

(* sort of (polymorphic) types *)
let ty_type = ty_app ts_type []

(* ts_type declaration *)
let d_ts_type = create_ty_decl [ts_type, Tabstract]

(* function symbol mapping ty_type^n to ty_type *)
let ls_of_ts = Wts.memoize 63 (fun ts ->
  let args = List.map (const ty_type) ts.ts_args in
  create_fsymbol (id_clone ts.ts_name) args ty_type)

(* function symbol selecting ty_type from ty_type^n *)
let ls_selects_of_ts = Wts.memoize 63 (fun ts ->
  let create_select _ =
    let preid = id_fresh ("select_"^ts.ts_name.id_string) in
    create_fsymbol preid [ty_type] ty_type in
  List.rev_map create_select ts.ts_args)

let ls_int_of_ty = create_fsymbol (id_fresh "int_of_ty") [ty_type] ty_int

(** definition of the previous selecting functions *)
let ls_selects_def_of_ts acc ts =
  let ls = ls_of_ts ts in
  let vars = List.rev_map
    (fun _ -> create_vsymbol (id_fresh "x") ty_type) ts.ts_args
  in
  let tvars = List.map t_var vars in
  (** type to int *)
  let id = string_of_int (id_hash ts.ts_name) in
  let acc =
    let t = fs_app ls tvars ty_type in
    let f = t_equ (fs_app ls_int_of_ty [t] ty_int) (t_int_const id) in
    let f = t_forall_close vars [[t]] f in
    let prsymbol = create_prsymbol (id_clone ts.ts_name) in
    create_prop_decl Paxiom prsymbol f :: acc
  in
  (** select *)
  let ls_selects = ls_selects_of_ts ts in
  let fmlas = List.rev_map2
    (fun ls_select value ->
      let t = fs_app ls tvars ty_type in
      let t = fs_app ls_select [t] ty_type in
      let f = t_equ t value in
      let f = t_forall_close vars [[t]] f in
      f)
    ls_selects tvars in
  let create_props ls_select fmla =
    let prsymbol = create_prsymbol (id_clone ls_select.ls_name) in
    create_prop_decl Paxiom prsymbol fmla in
  let props =
    List.fold_left2 (fun acc x y -> create_props x y::acc)
      acc ls_selects fmlas in
  let add acc fs = create_logic_decl [fs,None] :: acc in
  List.fold_left add props ls_selects

(* convert a type to a term of type ty_type *)
let rec term_of_ty tvmap ty = match ty.ty_node with
  | Tyvar tv ->
      Mtv.find tv tvmap
  | Tyapp (ts,tl) ->
      fs_app (ls_of_ts ts) (List.map (term_of_ty tvmap) tl) ty_type

(* rewrite a closed formula modulo its free typevars *)
let type_close tvs fn f =
  let get_vs tv = create_vsymbol (id_clone tv.tv_name) ty_type in
  let tvm = Mtv.mapi (fun v () -> get_vs v) tvs in
  let vl = Mtv.values tvm in
  let tvm = Mtv.map t_var tvm in
  t_forall_close_simp vl [] (fn tvm f)

let t_type_close fn f =
  let tvs = t_ty_freevars Stv.empty f in
  type_close tvs fn f

(* convert a type declaration to a list of lsymbol declarations *)
let lsdecl_of_tydecl acc td = match td with
    | ts, Talgebraic _ ->
        let ty = ty_app ts (List.map ty_var ts.ts_args) in
        Printer.unsupportedType ty "no algebraic types at this point"
    | { ts_def = Some _ }, _ -> acc
    | ts, _ -> create_logic_decl [ls_of_ts ts, None] :: acc

(* convert a type declaration to a list of lsymbol declarations *)
let lsdecl_of_tydecl_select tdl =
  let add acc td = match td with
    | ts, Talgebraic _ ->
        let ty = ty_app ts (List.map ty_var ts.ts_args) in
        Printer.unsupportedType ty "no algebraic types at this point"
    | { ts_def = Some _ }, _ -> acc
    | ts, _ -> ls_selects_def_of_ts acc ts
  in
  let defs = List.fold_left add [] tdl in
  List.fold_left lsdecl_of_tydecl defs tdl

let lsdecl_of_tydecl tdl = List.fold_left lsdecl_of_tydecl [] tdl

(* convert a constant to a functional symbol of type ty_base *)
let ls_of_const =
  let ht = Hterm.create 63 in
  fun t -> match t.t_node with
    | Tconst _ ->
        begin try Hterm.find ht t with Not_found ->
          let s = "const_" ^ Pp.string_of_wnl Pretty.print_term t in
          let ls = create_fsymbol (id_fresh s) [] ty_base in
          Hterm.add ht t ls;
          ls
        end
    | _ -> assert false

(* unprotected and unprotecting idents *)

let unprotected_label = "encoding : unprotected"
let unprotecting_label = "encoding : unprotecting"

let id_unprotected n = id_fresh ~label:[unprotected_label] n
let id_unprotecting n = id_fresh ~label:[unprotecting_label] n

let is_protected_id id = not (List.mem unprotected_label id.id_label)
let is_protecting_id id = not (List.mem unprotecting_label id.id_label)

let is_protected_vs kept vs =
  is_protected_id vs.vs_name && Sty.mem vs.vs_ty kept

let is_protected_ls kept ls =
  is_protected_id ls.ls_name && Sty.mem (of_option ls.ls_value) kept

(* monomorphise modulo the set of kept types * and an lsymbol map *)

let vs_monomorph kept vs =
  if is_protected_vs kept vs then vs else
  create_vsymbol (id_clone vs.vs_name) ty_base

let rec t_monomorph kept lsmap consts vmap t =
  let t_mono = t_monomorph kept lsmap consts in
  t_label_copy t (match t.t_node with
    | Tvar v ->
        Mvs.find v vmap
    | Tconst _ when Sty.mem (t_type t) kept ->
        t
    | Tconst _ ->
        let ls = ls_of_const t in
        consts := Sls.add ls !consts;
        fs_app ls [] ty_base
    | Tapp (ps,[t1;t2]) when ls_equal ps ps_equ ->
        t_equ (t_mono vmap t1) (t_mono vmap t2)
    | Tapp (ls,tl) ->
        let ls = lsmap ls in
        t_app ls (List.map (t_mono vmap) tl) ls.ls_value
    | Tif (f,t1,t2) ->
        t_if (t_mono vmap f) (t_mono vmap t1) (t_mono vmap t2)
    | Tlet (t1,b) ->
        let u,t2,close = t_open_bound_cb b in
        let v = vs_monomorph kept u in
        let t2 = t_mono (Mvs.add u (t_var v) vmap) t2 in
        t_let (t_mono vmap t1) (close v t2)
    | Tcase _ ->
        Printer.unsupportedTerm t "no match expressions at this point"
    | Teps b ->
        let u,f,close = t_open_bound_cb b in
        let v = vs_monomorph kept u in
        let f = t_mono (Mvs.add u (t_var v) vmap) f in
        t_eps (close v f)
    | Tquant (q,b) ->
        let ul,tl,f1,close = t_open_quant_cb b in
        let vl = List.map (vs_monomorph kept) ul in
        let add acc u v = Mvs.add u (t_var v) acc in
        let vmap = List.fold_left2 add vmap ul vl in
        let tl = tr_map (t_mono vmap) tl in
        t_quant q (close vl tl (t_mono vmap f1))
    | Tbinop (op,f1,f2) ->
        t_binary op (t_mono vmap f1) (t_mono vmap f2)
    | Tnot f1 ->
        t_not (t_mono vmap f1)
    | Ttrue | Tfalse ->
        t)

let d_monomorph kept lsmap d =
  let consts = ref Sls.empty in
  let kept = Sty.add ty_base kept in
  let t_mono = t_monomorph kept lsmap consts in
  let dl = match d.d_node with
    | Dtype tdl ->
        let add td acc = match td with
          | _, Talgebraic _ ->
              Printer.unsupportedDecl d "no algebraic types at this point"
          | { ts_def = Some _ }, _ -> acc
          | ts, _ when not (Sty.exists (ty_s_any (ts_equal ts)) kept) -> acc
          | _ -> create_ty_decl [td] :: acc
        in
        List.fold_right add tdl []
    | Dlogic ldl ->
        let conv (ls,ld) =
          let ls =
            if ls_equal ls ps_equ then ls else lsmap ls
          in
          match ld with
          | Some ld ->
              let ul,e,close = open_ls_defn_cb ld in
              let vl = List.map (vs_monomorph kept) ul in
              let add acc u v = Mvs.add u (t_var v) acc in
              let vmap = List.fold_left2 add Mvs.empty ul vl in
              close ls vl (t_mono vmap e)
          | None ->
              ls, None
        in
        [create_logic_decl (List.map conv ldl)]
    | Dind idl ->
        let iconv (pr,f) = pr, t_mono Mvs.empty f in
        let conv (ls,il) = lsmap ls, List.map iconv il in
        [create_ind_decl (List.map conv idl)]
    | Dprop (k,pr,f) ->
        [create_prop_decl k pr (t_mono Mvs.empty f)]
  in
  let add ls acc = create_logic_decl [ls,None] :: acc in
  Sls.fold add !consts dl

(* replace type variables in a goal with fresh type constants *)
let monomorphise_goal = Trans.goal (fun pr f ->
  let stv = t_ty_freevars Stv.empty f in
  if Stv.is_empty stv then [create_prop_decl Pgoal pr f] else
  let mty,ltv = Stv.fold (fun tv (mty,ltv) ->
    let ts = create_tysymbol (id_clone tv.tv_name) [] None in
    Mtv.add tv (ty_app ts []) mty, ts::ltv) stv (Mtv.empty,[]) in
  let f = t_ty_subst mty Mvs.empty f in
  List.fold_left
    (fun acc ts -> create_ty_decl [ts,Tabstract] :: acc)
    [create_prop_decl Pgoal pr f] ltv)

(* close by subtype the set of types tagged by meta_kept *)
let close_kept =
  Trans.on_tagged_ty meta_kept (fun kept ->
    let rec add acc ty = ty_fold add (Sty.add ty acc) ty in
    let kept' = Sty.fold (Util.flip add) kept kept in
    if kept == kept' then Trans.identity
    else
      let kept' = Sty.diff kept' kept in
      let fold ty acc = create_meta meta_kept [MAty ty] :: acc in
      Trans.add_tdecls (Sty.fold fold kept' []))

(* reconstruct a definition of an lsymbol or make a defining axiom *)
let defn_or_axiom ls f =
  match Decl.ls_defn_of_axiom f with
    | Some ld -> [create_logic_decl [ld]]
    | None ->
        let nm = ls.ls_name.id_string ^ "_def" in
        let pr = create_prsymbol (id_derive nm ls.ls_name) in
        [create_logic_decl [ls,None]; create_prop_decl Paxiom pr f]
