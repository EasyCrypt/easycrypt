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

type flag
(* Flag used for debugging only part of Why3 *)

val register_flag : string -> flag
(** Register a new flag. If someone try to register two times the same
    flag the same one is used *)

val lookup_flag : string -> flag
val list_flags : unit -> (string * flag * bool) list
(** List the known flags *)

(** Modify the state of a flag *)
val set_flag : flag -> unit
val unset_flag : flag -> unit
val toggle_flag : flag -> unit

val test_flag : flag -> bool
(** Return the state of the flag *)
val nottest_flag : flag -> bool

val set_debug_formatter : Format.formatter -> unit
(** Set the formatter used when printing debug material *)

val get_debug_formatter : unit -> Format.formatter
(** Get the formatter used when printing debug material *)


val dprintf : flag -> ('a, Format.formatter, unit) format -> 'a
(** Print only if the flag is set *)

val stack_trace : flag
(** stack_trace flag *)
