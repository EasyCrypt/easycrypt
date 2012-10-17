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
open Task
open Theory
open Task
open Decl
open Encoding

let make_pont ty () =
  let t2tb =
    let t2tb_name = "t2tb" in
    let t2tb_id = Libencoding.id_unprotected t2tb_name in
    create_fsymbol t2tb_id [ty] ty in
  let tb2t =
    let tb2t_name = "tb2t" in
    let tb2t_id = Libencoding.id_unprotecting tb2t_name in
    create_fsymbol tb2t_id [ty] ty in
  let t2tb_def = create_logic_decl [t2tb,None] in
  let tb2t_def = create_logic_decl [tb2t,None] in
  let bridge_l =
    let x_vs = create_vsymbol (id_fresh "i") ty in
    let x_t = t_var x_vs in
    let t2tb_x = fs_app t2tb [x_t] ty in
    let tb2t_t2tb_x = fs_app tb2t [t2tb_x] ty in
    let eq = t_equ tb2t_t2tb_x x_t in
    let ax = t_forall_close [x_vs] [[t2tb_x]] eq in
    let pr = create_prsymbol (id_fresh "BridgeL") in
    create_prop_decl Paxiom pr ax in
  let bridge_r =
    let x_vs = create_vsymbol (Libencoding.id_unprotected "j") ty in
    let x_t = t_var x_vs in
    let tb2t_x = fs_app tb2t [x_t] ty in
    let t2tb_tb2t_x = fs_app t2tb [tb2t_x] ty in
    let eq = t_equ t2tb_tb2t_x x_t in
    let ax = t_forall_close [x_vs] [[t2tb_tb2t_x]] eq in
    let pr = create_prsymbol (id_fresh "BridgeR") in
    create_prop_decl Paxiom pr ax in
  t2tb, tb2t, [t2tb_def; tb2t_def; bridge_l; bridge_r]

let seen = Hty.create 7

let add_decls tenv decls =
  let add ty () decls =
    let _,_,defs = Mty.find ty tenv in
    List.append defs decls in
  let decls = Hty.fold add seen decls in
  Hty.clear seen;
  decls

let conv_arg tenv t aty =
  let tty = t_type t in
  if ty_equal tty aty then t else
  try
    let t2tb,tb2t,_ = Mty.find tty tenv in
    Hty.replace seen tty ();
    match t.t_node with
      | Tapp (fs,[t]) when ls_equal fs tb2t -> t
      | _ -> fs_app t2tb [t] tty
  with Not_found -> t

let conv_app tenv fs tl tty =
  let t = fs_app fs tl tty in
  let vty = Util.of_option fs.ls_value in
  if ty_equal tty vty then t else
  try
    let _,tb2t,_ = Mty.find tty tenv in
    Hty.replace seen tty ();
    fs_app tb2t [t] tty
  with Not_found -> t

(* FIXME? in quantifiers we might generate triggers
   with unnecessary bridge functions over them *)
let rec rewrite tenv t = match t.t_node with
  | Tapp (ls,[t1;t2]) when ls_equal ls ps_equ ->
      t_equ (rewrite tenv t1) (rewrite tenv t2)
  | Tapp (ls,tl) ->
      let tl = List.map (rewrite tenv) tl in
      let tl = List.map2 (conv_arg tenv) tl ls.ls_args in
      if t.t_ty = None then ps_app ls tl
      else conv_app tenv ls tl (t_type t)
  | _ -> t_map (rewrite tenv) t

let decl tenv d = match d.d_node with
  | Dtype [_,Tabstract] -> [d]
  | Dtype _ -> Printer.unsupportedDecl d
      "Algebraic and recursively-defined types are \
            not supported, run eliminate_algebraic"
  | Dlogic [_, None] -> [d]
  | Dlogic [ls, Some ld] when not (Sid.mem ls.ls_name d.d_syms) ->
      let f = rewrite tenv (ls_defn_axiom ld) in
      Libencoding.defn_or_axiom ls f
  | Dlogic _ -> Printer.unsupportedDecl d
      "Recursively defined symbols are not supported, run eliminate_recursion"
  | Dind _ -> Printer.unsupportedDecl d
      "Inductive predicates are not supported, run eliminate_inductive"
  | Dprop (k,pr,f) ->
      [create_prop_decl k pr (rewrite tenv f)]

let decl tenv d =
  let decls = decl tenv d in
  add_decls tenv decls

let t = Trans.on_tagged_ty Libencoding.meta_kept (fun s ->
  Trans.decl (decl (Mty.mapi make_pont s)) None)

(* Every finite protected type has a finite twin type. But
   as we do not introduce twin types explicitly, we declare
   a dummy type constant finite. This is enough to trigger
   the safety in Encoding_explicit. *)

let ts_dummy = Ty.create_tysymbol (id_fresh "finite_twin_type") [] None

let enum =
  Trans.on_tagged_ty Libencoding.meta_kept (fun kept ->
  Trans.on_tagged_ts Eliminate_algebraic.meta_enum (fun enum ->
  Trans.on_meta Eliminate_algebraic.meta_phantom (fun phlist ->
    let finite_ty = Eliminate_algebraic.is_finite_ty enum phlist in
    if not (Sty.exists finite_ty kept) then Trans.identity else
      Trans.add_tdecls [create_meta Eliminate_algebraic.meta_enum
        [MAts ts_dummy]])))

let twin = const (Trans.compose t enum)

let () = Hashtbl.replace Encoding.ft_enco_kept "twin" twin
