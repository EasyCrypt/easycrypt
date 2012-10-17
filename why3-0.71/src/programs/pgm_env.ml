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

open Why3
open Util
open Theory
open Pgm_module

type module_file = Theory.theory Mstr.t * Pgm_module.t Mstr.t

type t = {
  env      : Env.env;
  retrieve : retrieve_module;
  memo     : (string list, module_file) Hashtbl.t;
}

and retrieve_module = t -> string list -> string -> in_channel -> module_file

let get_env penv = penv.env

let create env retrieve = {
  env = env;
  retrieve = retrieve;
  memo = Hashtbl.create 17;
}

exception ModuleNotFound of string list * string

let find_library penv sl =
  try
    Hashtbl.find penv.memo sl
  with Not_found ->
    Hashtbl.add penv.memo sl (Mstr.empty, Mstr.empty);
    let file, c = Env.find_channel penv.env "whyml" sl in
    let r = penv.retrieve penv sl file c in
    close_in c;
    Hashtbl.replace penv.memo sl r;
    r

let find_module penv sl s =
  try Mstr.find s (snd (find_library penv sl))
  with Not_found -> raise (ModuleNotFound (sl, s))
