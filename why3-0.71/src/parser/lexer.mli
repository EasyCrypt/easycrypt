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

(** parsing entry points *)

val parse_logic_file :
  Env.env -> string list -> Lexing.lexbuf -> Theory.theory Util.Mstr.t

val parse_program_file : Lexing.lexbuf -> Ptree.program_file

(** other functions to be re-used in other lexers/parsers *)

val newline : Lexing.lexbuf -> unit

val comment : Lexing.lexbuf -> unit

val string : Lexing.lexbuf -> string

val remove_leading_plus : string -> string

val with_location : (Lexing.lexbuf -> 'a) -> Lexing.lexbuf -> 'a
