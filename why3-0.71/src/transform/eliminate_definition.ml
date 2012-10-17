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
open Term
open Decl

(** Discard definitions of built-in symbols *)

let add_ld q = function
  | ls, Some _ when Sls.mem ls q -> (ls, None)
  | d -> d

let add_id q (ld,id) = function
  | ls, _ when Sls.mem ls q -> (ls, None)::ld, id
  | d -> ld, d::id

let elim q spr d = match d.d_node with
  | Dlogic l ->
      [create_logic_decl (List.map (add_ld q) l)]
  | Dind l ->
      let ld, id = List.fold_left (add_id q) ([],[]) l in
      let ld = if ld = [] then [] else [create_logic_decl (List.rev ld)] in
      let id = if id = [] then [] else [create_ind_decl   (List.rev id)] in
      ld @ id
  | Dprop (Paxiom,pr,_) when Spr.mem pr spr -> []
  | _ -> [d]

let eliminate_builtin =
  Trans.on_tagged_ls Printer.meta_syntax_logic (fun rem_ls ->
  Trans.on_tagged_pr Printer.meta_remove_prop  (fun rem_pr ->
  Trans.decl (elim rem_ls rem_pr) None))

let () = Trans.register_transform "eliminate_builtin" eliminate_builtin

(** Eliminate definitions of functions and predicates *)

let rec t_insert hd t = match t.t_node with
  | Tif (f1,t2,t3) ->
      t_if f1 (t_insert hd t2) (t_insert hd t3)
  | Tlet (t1,bt) ->
      let v,t2 = t_open_bound bt in
      t_let_close v t1 (t_insert hd t2)
  | Tcase (tl,bl) ->
      let br b =
        let pl,t1 = t_open_branch b in
        t_close_branch pl (t_insert hd t1)
      in
      t_case tl (List.map br bl)
  | _ -> TermTF.t_selecti t_equ_simp t_iff_simp hd t

let add_ld func pred axl = function
  | ls, Some ld when (if ls.ls_value = None then pred else func) ->
      let vl,e = open_ls_defn ld in
      let nm = ls.ls_name.id_string ^ "_def" in
      let hd = t_app ls (List.map t_var vl) e.t_ty in
      let ax = t_forall_close vl [] (t_insert hd e) in
      let pr = create_prsymbol (id_derive nm ls.ls_name) in
      create_prop_decl Paxiom pr ax :: axl, (ls, None)
  | d ->
      axl, d

let elim_decl func pred l =
  let axl, l = map_fold_left (add_ld func pred) [] l in
  create_logic_decl l :: List.rev axl

let elim func pred d = match d.d_node with
  | Dlogic l -> elim_decl func pred l
  | _ -> [d]

let elim_recursion d = match d.d_node with
  | Dlogic ([s,_] as l)
    when Sid.mem s.ls_name d.d_syms -> elim_decl true true l
  | Dlogic l when List.length l > 1 -> elim_decl true true l
  | _ -> [d]

let is_struct dl =
  try
    Mls.for_all (fun _ il -> List.length il = 1) (check_termination dl)
  with NoTerminationProof _ ->
    false

let elim_non_struct_recursion d = match d.d_node with
  | Dlogic ((s,_) :: _ as dl)
    when Sid.mem s.ls_name d.d_syms && not (is_struct dl) ->
      elim_decl true true dl
  | _ ->
      [d]

let elim_mutual d = match d.d_node with
  | Dlogic l when List.length l > 1 -> elim_decl true true l
  | _ -> [d]

let eliminate_definition_func  = Trans.decl (elim true false) None
let eliminate_definition_pred  = Trans.decl (elim false true) None
let eliminate_definition       = Trans.decl (elim true true) None
let eliminate_recursion        = Trans.decl elim_recursion None
let eliminate_non_struct_recursion = Trans.decl elim_non_struct_recursion None
let eliminate_mutual_recursion = Trans.decl elim_mutual None

let () =
  Trans.register_transform "eliminate_definition_func"
    eliminate_definition_func;
  Trans.register_transform "eliminate_definition_pred"
    eliminate_definition_pred;
  Trans.register_transform "eliminate_definition"
    eliminate_definition;
  Trans.register_transform "eliminate_recursion"
    eliminate_recursion;
  Trans.register_transform "eliminate_non_struct_recursion"
    eliminate_non_struct_recursion;
  Trans.register_transform "eliminate_mutual_recursion"
    eliminate_mutual_recursion

