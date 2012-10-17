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
open Theory
open Pgm_module

type t

val get_env : t -> Env.env

type module_file = Theory.theory Util.Mstr.t * Pgm_module.t Util.Mstr.t

type retrieve_module = t -> string list -> string -> in_channel -> module_file

val create : Env.env -> retrieve_module -> t

exception ModuleNotFound of string list * string

val find_module : t -> string list -> string -> Pgm_module.t
  (** [find_module e p n] finds the module named [p.n] in environment [e]
      @raise ModuleNotFound if module not present in env [e] *)
