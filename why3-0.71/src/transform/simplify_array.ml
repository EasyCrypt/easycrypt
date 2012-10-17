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
open Theory
open Env

let prelude = ["array"]
let array = "Array"
let store = ["store"]
let select = ["select"]

let make_rt_rf env =
  let array  =
    try
      find_theory env prelude array
    with TheoryNotFound (_,s) ->
      Format.eprintf "The theory %s is unknown" s;
      exit 1 in
  let store  = (ns_find_ls array.th_export store).ls_name in
  let select = (ns_find_ls array.th_export select).ls_name in
  let rec rt t =
    let t = TermTF.t_map rt rf t in
    match t.t_node with
      | Tapp (lselect,[{t_node=Tapp(lstore,[_;a1;b])};a2])
          when lselect.ls_name == select &&
            lstore.ls_name == store &&
            t_equal_alpha a1 a2 -> b
      | _ -> t
  and rf f = TermTF.t_map rt rf f  in
  rt,rf

let t env = let rt,rf = make_rt_rf env in Trans.rewriteTF rt rf None

let () = Trans.register_env_transform "simplify_array" t
