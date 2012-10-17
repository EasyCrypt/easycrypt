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

(*
  This module was poorly designed by Claude Marché, with the
  enormous help of Jean-Christophe Filliâtre and Andrei Paskevich
  for finding the right function in the Why3 API
*)

open Ident
open Term
open Decl
open Task

let rec intros pr f = match f.t_node with
  | Tbinop (Timplies,f1,f2) ->
      (* split f1 *)
      let l = Split_goal.split_pos f1 in
      List.fold_right
        (fun f acc ->
           let id = create_prsymbol (id_fresh "H") in
           let d = create_prop_decl Paxiom id f in
           d :: acc)
        l
        (intros pr f2)
  | Tquant (Tforall,fq) ->
      let vsl,_trl,f = t_open_quant fq in
      let intro_var subst vs =
        let ls = create_lsymbol (id_clone vs.vs_name) [] (Some vs.vs_ty) in
        Mvs.add vs (fs_app ls [] vs.vs_ty) subst,
        create_logic_decl [ls,None]
      in
      let subst, dl = Util.map_fold_left intro_var Mvs.empty vsl in
      let f = t_subst subst f in
      dl @ intros pr f
  | Tlet (t,fb) ->
      let vs,f = t_open_bound fb in
      let ls = create_lsymbol (id_clone vs.vs_name) [] (Some vs.vs_ty) in
      let f = t_subst_single vs (fs_app ls [] vs.vs_ty) f in
      let d = create_logic_decl [make_ls_defn ls [] t] in
      d :: intros pr f
  | _ -> [create_prop_decl Pgoal pr f]

let () = Trans.register_transform "introduce_premises" (Trans.goal intros)

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. byte"
End:
*)
