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

let protect tenv hls t =
  try
    let ty = t_type t in
    let fs = Mty.find ty tenv in
    Hls.replace hls fs ();
    fs_app fs [t] ty
  with
    | Not_found -> t

let rec rewrite_term tenv hls t = match t.t_node with
  | Tapp (fs,tl) ->
      let pin t = protect tenv hls (rewrite_term tenv hls t) in
      t_app fs (List.map pin tl) t.t_ty
  | _ -> t_map (rewrite_term tenv hls) t

let decl tenv d = match d.d_node with
  | Dtype [_,Tabstract] -> [d]
  | Dtype _ -> Printer.unsupportedDecl d
      "Algebraic and recursively-defined types are \
            not supported, run eliminate_algebraic"
  | Dlogic [_, None] -> [d]
  | Dlogic [ls, Some ld] when not (Sid.mem ls.ls_name d.d_syms) ->
      let hls = Hls.create 7 in
      let f = rewrite_term tenv hls (ls_defn_axiom ld) in
      let decl fs () decls = create_logic_decl [fs,None] :: decls in
      Hls.fold decl hls (Libencoding.defn_or_axiom ls f)
  | Dlogic _ -> Printer.unsupportedDecl d
      "Recursively-defined symbols are not supported, run eliminate_recursion"
  | Dind _ -> Printer.unsupportedDecl d
      "Inductive predicates are not supported, run eliminate_inductive"
  | _ ->
      let hls = Hls.create 7 in
      let d = decl_map (rewrite_term tenv hls) d in
      let decl fs () decls = create_logic_decl [fs,None] :: decls in
      Hls.fold decl hls [d]

let protect_enumeration =
  Trans.on_tagged_ty Libencoding.meta_kept (fun kept ->
  Trans.on_tagged_ts Eliminate_algebraic.meta_enum (fun enum ->
  Trans.on_meta Eliminate_algebraic.meta_phantom (fun phlist ->
    let finite_ty = Eliminate_algebraic.is_finite_ty enum phlist in
    let add_protect ty tenv =
      if not (finite_ty ty) then tenv else
      let ts = match ty.ty_node with Tyapp (s,_) -> s | _ -> assert false in
      let id = id_fresh ("protect_enum_" ^ ts.ts_name.id_string) in
      let fs = create_fsymbol id [ty] ty in
      Mty.add ty fs tenv
    in
    let tenv = Sty.fold add_protect kept Mty.empty in
    Trans.decl (decl tenv) None)))

