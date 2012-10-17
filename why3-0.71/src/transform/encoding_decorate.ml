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
open Libencoding

(* From Encoding Polymorphism CADE07*)

(* polymorphic decoration function *)
let ls_poly_deco =
  let tyvar = ty_var (create_tvsymbol (id_fresh "a")) in
  create_fsymbol (id_fresh "sort") [ty_type;tyvar] tyvar

let decorate tvar t =
  let tty = term_of_ty tvar (t_type t) in
  t_app ls_poly_deco [tty;t] t.t_ty

let deco_term kept tvar =
  let rec deco t = match t.t_node with
    | Tvar v ->
        if is_protected_vs kept v
        then t else decorate tvar t
    | Tapp (ls,_) ->
        let t = t_map deco t in
        if ls.ls_value = None || is_protected_ls kept ls
        then t else decorate tvar t
    | Tconst _ ->
        if Sty.mem (t_type t) kept
        then t else decorate tvar t
    | Tlet (t1,tb) ->
        let v,e,close = t_open_bound_cb tb in
        t_let (t_map deco t1) (close v (deco e))
    | Teps tb ->
        let v,f,close = t_open_bound_cb tb in
        let t = t_eps (close v (deco f)) in
        if is_protected_vs kept v
        then t else decorate tvar t
    | _ -> t_map deco t
  in
  deco

let deco_decl kept d = match d.d_node with
  | Dtype tdl ->
      d :: lsdecl_of_tydecl tdl
  | Dlogic [_, None] -> [d]
  | Dlogic [ls, Some ld] when not (Sid.mem ls.ls_name d.d_syms) ->
      let f = t_type_close (deco_term kept) (ls_defn_axiom ld) in
      defn_or_axiom ls f
  | Dlogic _ -> Printer.unsupportedDecl d
      "Recursively-defined symbols are not supported, run eliminate_recursion"
  | Dind _ -> Printer.unsupportedDecl d
      "Inductive predicates are not supported, run eliminate_inductive"
  | Dprop (k,pr,f) ->
      [create_prop_decl k pr (t_type_close (deco_term kept) f)]

let d_poly_deco = create_logic_decl [ls_poly_deco, None]

let deco_init =
  let init = Task.add_decl None d_ts_type in
  let init = Task.add_decl init d_poly_deco in
  init

let deco kept = Trans.decl (deco_decl kept) deco_init

(** Monomorphisation *)

let ts_deco = create_tysymbol (id_fresh "deco") [] None
let ty_deco = ty_app ts_deco []
let ls_deco = create_fsymbol (id_fresh "sort") [ty_type;ty_base] ty_deco

(* monomorphise a logical symbol *)
let lsmap kept = Wls.memoize 63 (fun ls ->
  if ls_equal ls ls_poly_deco then ls_deco else
  let prot_arg = is_protecting_id ls.ls_name in
  let prot_val = is_protected_id ls.ls_name in
  let neg ty = if prot_arg && Sty.mem ty kept then ty else ty_deco in
  let pos ty = if prot_val && Sty.mem ty kept then ty else ty_base in
  let tyl = List.map neg ls.ls_args in
  let tyr = Util.option_map pos ls.ls_value in
  if Util.option_eq ty_equal tyr ls.ls_value
     && List.for_all2 ty_equal tyl ls.ls_args then ls
  else create_lsymbol (id_clone ls.ls_name) tyl tyr)

let d_ts_base = create_ty_decl [ts_base, Tabstract]
let d_ts_deco = create_ty_decl [ts_deco, Tabstract]

let mono_init =
  let init = Task.add_decl None d_ts_base in
  let init = Task.add_decl init d_ts_deco in
  init

let mono kept =
  let kept = Sty.add ty_type kept in
  Trans.decl (d_monomorph kept (lsmap kept)) mono_init

let t = Trans.on_tagged_ty Libencoding.meta_kept (fun kept ->
  Trans.compose (deco kept) (mono kept))

let () = Hashtbl.replace Encoding.ft_enco_poly "decorate" (const t)

