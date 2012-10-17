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

open Term

let make_rt_rf keep =
  let rec rt t = TermTF.t_map rt rf t
  and rf f =
    let f = TermTF.t_map rt rf f in
    match f.t_node with
      | Tquant (Tforall,fq) ->
        let vsl,trl,f2 = t_open_quant fq in
        let one_false = ref false in
        let keep x = let b = keep x in
                     if b then b else (one_false := true; b) in
        let trl = List.filter (List.for_all keep) trl in
        if not (!one_false) then f else t_forall_close vsl trl f2
      | _ -> f in
  rt,rf



let keep_no_trigger _ = false


let remove_triggers =
    let rt,rf = make_rt_rf keep_no_trigger in
    Trans.rewriteTF rt rf None

let () = Trans.register_transform "remove_triggers" remove_triggers


let keep_no_predicate e = e.t_ty <> None

let filter_trigger_no_predicate =
    let rt,rf = make_rt_rf keep_no_predicate in
    Trans.rewriteTF rt rf None

let () = Trans.register_transform "filter_trigger_no_predicate"
  filter_trigger_no_predicate


let keep_no_fmla = function
  | { t_ty = Some _ } -> true
  | { t_node = Tapp (ps,_) } -> not (ls_equal ps ps_equ)
  | _ -> false

let filter_trigger =
    let rt,rf = make_rt_rf keep_no_fmla in
    Trans.rewriteTF rt rf None

let () = Trans.register_transform "filter_trigger" filter_trigger


let keep_no_builtin rem_ls = function
  | { t_ty = Some _ } -> true
  | { t_node = Tapp (ps,_) } -> not (Sls.mem ps rem_ls)
  | _ -> false


let filter_trigger_builtin =
  Trans.on_tagged_ls Printer.meta_syntax_logic (fun rem_ls ->
    let rt,rf = make_rt_rf (keep_no_builtin rem_ls) in
    Trans.rewriteTF rt rf None)

let () = Trans.register_transform "filter_trigger_builtin"
  filter_trigger_builtin
