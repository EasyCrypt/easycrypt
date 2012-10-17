(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2011                                                    *)
(*    Guillaume Melquiond                                                 *)
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

open Decl
open Term
open Ty

let instantiate_prop expr args values =
  let add (mt,mv) x y = ty_match mt x.vs_ty (t_type y), Mvs.add x y mv in
  let (mt,mv) = List.fold_left2 add (Mtv.empty, Mvs.empty) args values in
  t_ty_subst mt mv expr

(** [trans spr task_hd ((lpr, past), task)] looks in [task_hd] for terms
    that can instantiate axioms of [lpr] and does so in [task]; [lpr] is
    progressively filled with the axioms of [spr] as they are
    encountered; [past] contains terms for which axioms have already been
    instantiated, so that they are not duplicated *)
let trans spr task_hd (((lpr, past), task) as current) =

  let rec scan_term ((past, task) as current) t =
    let current =
      if t.t_ty = None || Sterm.mem t past then current else
      (
        Sterm.add t past,
        List.fold_right (fun (quant, e) task ->
          try
            let ax = instantiate_prop e quant [t] in
            let pr = create_prsymbol (Ident.id_fresh "auto_instance") in
            Task.add_decl task (create_prop_decl Paxiom pr ax)
          with TypeMismatch _ -> task
        ) lpr task
      ) in
    match t.t_node with
    | Tapp _
    | Tbinop _
    | Tnot _ ->
        t_fold scan_term current t
    | _ -> current in

  let (current, task) =
    match task_hd.Task.task_decl.Theory.td_node with
    | Theory.Decl { d_node = Dprop (_,pr,expr) } ->
        let (past, task) = scan_term (past, task) expr in
        let lpr = if not (Spr.mem pr spr) then lpr else
          match expr.t_node with
          | Tquant (Tforall,q_expr) ->
              let (quant, _, expr) = t_open_quant q_expr in
              assert (List.length quant = 1);
              (quant, expr) :: lpr
          | _ -> assert false in
        ((lpr, past), task)
    | _ -> current in
  (current, Task.add_tdecl task task_hd.Task.task_decl)

let meta = Theory.register_meta "instantiate : auto" [Theory.MTprsymbol]

(** all the symbols (unary predicates) that have the "instantiate : auto"
    meta are marked for instantiation by the above transformation *)
let () =
  Trans.register_transform "instantiate_predicate"
    (Trans.on_tagged_pr meta (fun spr ->
      Trans.fold_map (trans spr) ([], Sterm.empty) None))
