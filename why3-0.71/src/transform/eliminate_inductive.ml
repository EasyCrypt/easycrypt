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

open Ident
open Term
open Decl
open Task

let log acc (ps,_) = create_logic_decl [ps, None] :: acc
let axm acc (pr,f) = create_prop_decl Paxiom pr f :: acc
let imp acc (_,al) = List.fold_left axm acc al

let exi vl (_,f) =
  let rec descend f = match f.t_node with
    | Tquant (Tforall,f) ->
        let vl,tl,f = t_open_quant f in
        t_exists_close vl tl (descend f)
    | Tbinop (Timplies,g,f) ->
        t_and g (descend f)
    | Tapp (_,tl) ->
        let marry acc v t = t_and_simp acc (t_equ v t) in
        List.fold_left2 marry t_true vl tl
    | _ -> assert false
  in
  descend f

let inv acc (ps,al) =
  let vl = List.map (create_vsymbol (id_fresh "z")) ps.ls_args in
  let tl = List.map t_var vl in
  let hd = ps_app ps tl in
  let dj = Util.map_join_left (exi tl) t_or al in
  let hsdj = Simplify_formula.fmla_remove_quant (t_implies hd dj) in
  let ax = t_forall_close vl [] hsdj in
  let nm = id_derive (ps.ls_name.id_string ^ "_inversion") ps.ls_name in
  create_prop_decl Paxiom (create_prsymbol nm) ax :: acc

let elim d = match d.d_node with
  | Dind il ->
      let dl = List.fold_left log [] il in
      let dl = List.fold_left imp dl il in
      let dl = List.fold_left inv dl il in
      List.rev dl
  | _ -> [d]

let eliminate_inductive = Trans.decl elim None

let () = Trans.register_transform "eliminate_inductive" eliminate_inductive

