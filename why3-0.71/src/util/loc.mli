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

open Format

(* Lexing locations *)

val current_offset : int ref
val reloc : Lexing.position -> Lexing.position
val set_file : string -> Lexing.lexbuf -> unit

val transfer_loc : Lexing.lexbuf -> Lexing.lexbuf -> unit

(* locations in files *)

type position

val extract : Lexing.position * Lexing.position -> position
val join : position -> position -> position

exception Located of position * exn

val dummy_position : position

val user_position : string -> int -> int -> int -> position

val get : position -> string * int * int * int

val compare : position -> position -> int
val equal : position -> position -> bool
val hash : position -> int

val gen_report_position : formatter -> position -> unit

val report_position : formatter -> position -> unit

