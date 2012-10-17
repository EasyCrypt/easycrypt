(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2011                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Johannes Kanig                                                      *)
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

open Theory
open Decl
open Task
open Term

let is_func_ty t =
  match t.Ty.ty_node with
  | Ty.Tyapp (s,_) ->
      Ty.ts_equal s Ty.ts_func || Ty.ts_equal s Ty.ts_pred
  | _ -> false

type lambda_match =
  | Flam of vsymbol list * trigger * term
  | Tlam of vsymbol list * trigger * term
  | LNone

let destruct_lambda t =
  match t.t_node with
  | Teps fb ->
      let fn, f = t_open_bound fb in
      if is_func_ty fn.vs_ty then
        begin match f.t_node with
        | Tquant (Tforall, fq) ->
            let args, trs, f = t_open_quant fq in
            begin match f.t_node with
            | Tbinop (Tiff,_,body) -> Flam (args, trs, body)
            | Tapp (ls,[_;body]) when ls_equal ls ps_equ ->
                Tlam (args, trs, body)
            | _ -> LNone end
        | _ -> LNone end
      else LNone
  | _ -> LNone

let is_lambda t = destruct_lambda t <> LNone

let rec rewriteT t =
  match t.t_node with
  | Teps fb when is_lambda t ->
      let fv = Mvs.keys t.t_vars in
      let x, f = t_open_bound fb in
      let f = rewriteF f in
      if fv = [] then t_eps_close x f
      else
        (* the type, symbol and term of the new epsilon-symbol [magic] *)
        let magic_ty =
          List.fold_right (fun x acc -> Ty.ty_func x.vs_ty acc) fv x.vs_ty in
        let magic_fs = create_vsymbol (Ident.id_fresh "f") magic_ty in
        let magic_f = t_var magic_fs in
        (* the application of [magic] to the free variables *)
        let rx =
          List.fold_left (fun acc x -> t_func_app acc (t_var x)) magic_f fv in
        (* substitute [magic] for [x] *)
        let f = t_subst_single x rx f in
        (* quantify over free variables and epsilon-close over [magic] *)
        let f = t_forall_close_merge fv f in
        let f = t_eps_close magic_fs f in
        (* apply epsilon-term to variables *)
        List.fold_left (fun acc x -> t_func_app acc (t_var x)) f fv
  | _ ->
      TermTF.t_map rewriteT rewriteF t

and rewriteF f = TermTF.t_map rewriteT rewriteF f

let close d = [DeclTF.decl_map rewriteT rewriteF d]

let close_epsilon =
  Trans.on_used_theory highord_theory (fun used ->
    if used then Trans.decl close None else Trans.identity)

let () = Trans.register_transform "close_epsilon" close_epsilon

(* TODO variable abstraction *)
