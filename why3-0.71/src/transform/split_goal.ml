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

let apply_append fn acc l =
  List.fold_left (fun l e -> fn e :: l) acc (List.rev l)

let apply_append2 fn acc l1 l2 =
  Util.list_fold_product (fun l e1 e2 -> fn e1 e2 :: l)
    acc (List.rev l1) (List.rev l2)

let split_case forig spl c acc tl bl =
  let bl = List.rev_map t_open_branch_cb bl in
  let bll,_ = List.fold_left (fun (bll,el) (pl,f,close) ->
    let spf = spl [] f in
    let brc = t_close_branch pl c in
    let bll = List.map (fun rl -> brc::rl) bll in
    let bll = apply_append (fun f -> close pl f :: el) bll spf in
    bll, brc::el) ([],[]) bl
  in
  let fn bl = t_label_copy forig (t_case tl bl) in
  apply_append fn acc bll

let asym_split = Term.asym_label
let stop_split = "stop_split"

let asym f = List.mem asym_split f.t_label
let stop f = List.mem stop_split f.t_label

let unstop f =
  let ll = List.filter ((<>) stop_split) f.t_label in
  t_label ?loc:f.t_loc ll f

let rec split_pos ro acc f = match f.t_node with
  | _ when ro && stop f -> unstop f :: acc
  | Ttrue -> acc
  | Tfalse -> f::acc
  | Tapp _ -> f::acc
  | Tbinop (Tand,f1,f2) when asym f ->
      split_pos ro (split_pos ro acc (t_implies f1 f2)) f1
  | Tbinop (Tand,f1,f2) ->
      split_pos ro (split_pos ro acc f2) f1
  | Tbinop (Timplies,f1,f2) when ro ->
      let fn f2 = t_label_copy f (t_implies f1 f2) in
      apply_append fn acc (split_pos ro [] f2)
  | Tbinop (Timplies,f1,f2) ->
      let fn f1 f2 = t_label_copy f (t_implies f1 f2) in
      apply_append2 fn acc (split_neg ro [] f1) (split_pos ro [] f2)
  | Tbinop (Tiff,f1,f2) ->
      let f12 = t_label_copy f (t_implies f1 f2) in
      let f21 = t_label_copy f (t_implies f2 f1) in
      split_pos ro (split_pos ro acc f21) f12
  | Tbinop (Tor,_,_) when ro -> f::acc
  | Tbinop (Tor,f1,f2) ->
      let fn f1 f2 = t_label_copy f (t_or f1 f2) in
      apply_append2 fn acc (split_pos ro [] f1) (split_pos ro [] f2)
  | Tnot f1 ->
      let fn f1 = t_label_copy f (t_not f1) in
      apply_append fn acc (split_neg ro [] f1)
  | Tif (fif,fthen,felse) ->
      let fit = t_label_copy f (t_implies fif fthen) in
      let fie = t_label_copy f (t_implies (t_not fif) felse) in
      split_pos ro (split_pos ro acc fie) fit
  | Tlet (t,fb) ->
      let vs,f1,close = t_open_bound_cb fb in
      let fn f1 = t_label_copy f (t_let t (close vs f1)) in
      apply_append fn acc (split_pos ro [] f1)
  | Tcase (tl,bl) ->
      split_case f (split_pos ro) t_true acc tl bl
  | Tquant (Tforall,fq) ->
      let vsl,trl,f1,close = t_open_quant_cb fq in
      let fn f1 = t_label_copy f (t_forall (close vsl trl f1)) in
      apply_append fn acc (split_pos ro [] f1)
  | Tquant (Texists,_) -> f::acc
  | Tvar _ | Tconst _ | Teps _ -> raise (FmlaExpected f)

and split_neg ro acc f = match f.t_node with
  | _ when ro && stop f -> unstop f :: acc
  | Ttrue -> f::acc
  | Tfalse -> acc
  | Tapp _ -> f::acc
  | Tbinop (Tand,_,_) when ro -> f::acc
  | Tbinop (Tand,f1,f2) ->
      let fn f1 f2 = t_label_copy f (t_and f1 f2) in
      apply_append2 fn acc (split_neg ro [] f1) (split_neg ro [] f2)
  | Tbinop (Timplies,f1,f2) when asym f ->
      split_neg ro (split_neg ro acc (t_and f1 f2)) (t_not f1)
  | Tbinop (Timplies,f1,f2) ->
      split_neg ro (split_neg ro acc f2) (t_not f1)
  | Tbinop (Tiff,f1,f2) ->
      let f12 = t_label_copy f (t_and f1 f2) in
      let f21 = t_label_copy f (t_and (t_not f1) (t_not f2)) in
      split_neg ro (split_neg ro acc f21) f12
  | Tbinop (Tor,f1,f2) when asym f ->
      split_neg ro (split_neg ro acc (t_and (t_not f1) f2)) f1
  | Tbinop (Tor,f1,f2) ->
      split_neg ro (split_neg ro acc f2) f1
  | Tnot f1 ->
      let fn f1 = t_label_copy f (t_not f1) in
      apply_append fn acc (split_pos ro [] f1)
  | Tif (fif,fthen,felse) ->
      let fit = t_label_copy f (t_and fif fthen) in
      let fie = t_label_copy f (t_and (t_not fif) felse) in
      split_neg ro (split_neg ro acc fie) fit
  | Tlet (t,fb) ->
      let vs,f1,close = t_open_bound_cb fb in
      let fn f1 = t_label_copy f (t_let t (close vs f1)) in
      apply_append fn acc (split_neg ro [] f1)
  | Tcase (tl,bl) ->
      split_case f (split_neg ro) t_false acc tl bl
  | Tquant (Texists,fq) ->
      let vsl,trl,f1,close = t_open_quant_cb fq in
      let fn f1 = t_label_copy f (t_exists (close vsl trl f1)) in
      apply_append fn acc (split_neg ro [] f1)
  | Tquant (Tforall,_) -> f::acc
  | Tvar _ | Tconst _ | Teps _ -> raise (FmlaExpected f)

let split_goal ro pr f =
  let make_prop f = [create_prop_decl Pgoal pr f] in
  List.map make_prop (split_pos ro [] f)

let split_axiom ro pr f =
  let make_prop f =
    let pr = create_prsymbol (id_clone pr.pr_name) in
    create_prop_decl Paxiom pr f in
  match split_pos ro [] f with
    | [f] -> [create_prop_decl Paxiom pr f]
    | fl  -> List.map make_prop fl

let split_all ro d = match d.d_node with
  | Dprop (Pgoal, pr,f) ->  split_goal  ro pr f
  | Dprop (Paxiom,pr,f) -> [split_axiom ro pr f]
  | _ -> [[d]]

let split_premise ro d = match d.d_node with
  | Dprop (Paxiom,pr,f) ->  split_axiom ro pr f
  | _ -> [d]

let full_split_pos = split_pos false []
let full_split_neg = split_neg false []

let split_pos = split_pos true []
let split_neg = split_neg true []

let full_split_goal    = Trans.goal_l (split_goal    false)
let full_split_all     = Trans.decl_l (split_all     false) None
let full_split_premise = Trans.decl   (split_premise false) None

let split_goal    = Trans.goal_l (split_goal    true)
let split_all     = Trans.decl_l (split_all     true) None
let split_premise = Trans.decl   (split_premise true) None

let () = Trans.register_transform_l "split_goal"    split_goal
let () = Trans.register_transform_l "split_all"     split_all
let () = Trans.register_transform   "split_premise" split_premise

let () = Trans.register_transform_l "full_split_goal"    full_split_goal
let () = Trans.register_transform_l "full_split_all"     full_split_all
let () = Trans.register_transform   "full_split_premise" full_split_premise

let ls_of_var v =
  create_fsymbol (id_fresh ("spl_" ^ v.vs_name.id_string)) [] v.vs_ty

let rec split_intro pr dl acc f =
  let rsp = split_intro pr dl in
  match f.t_node with
  | Ttrue -> acc
  | Tbinop (Tand,f1,f2) when asym f ->
      rsp (rsp acc (t_implies f1 f2)) f1
  | Tbinop (Tand,f1,f2) ->
      rsp (rsp acc f2) f1
  | Tbinop (Timplies,f1,f2) ->
      let pp = create_prsymbol (id_fresh (pr.pr_name.id_string ^ "_spl")) in
      let dl = create_prop_decl Paxiom pp f1 :: dl in
      split_intro pr dl acc f2
  | Tbinop (Tiff,f1,f2) ->
      rsp (rsp acc (t_implies f2 f1)) (t_implies f1 f2)
  | Tif (fif,fthen,felse) ->
      rsp (rsp acc (t_implies (t_not fif) felse)) (t_implies fif fthen)
  | Tlet (t,fb) -> let vs,f = t_open_bound fb in
      let ls = ls_of_var vs in
      let f  = t_subst_single vs (fs_app ls [] vs.vs_ty) f in
      let dl = create_logic_decl [make_ls_defn ls [] t] :: dl in
      split_intro pr dl acc f
  | Tquant (Tforall,fq) -> let vsl,_,f = t_open_quant fq in
      let lls = List.map ls_of_var vsl in
      let add s vs ls = Mvs.add vs (fs_app ls [] vs.vs_ty) s in
      let f = t_subst (List.fold_left2 add Mvs.empty vsl lls) f in
      let add dl ls = create_logic_decl [ls, None] :: dl in
      let dl = List.fold_left add dl lls in
      split_intro pr dl acc f
  | _ ->
      let goal f = List.rev (create_prop_decl Pgoal pr f :: dl) in
      List.rev_append (List.rev_map goal (split_pos f)) acc

let split_intro = Trans.goal_l (fun pr f -> split_intro pr [] [] f)

let () = Trans.register_transform_l "split_intro" split_intro

