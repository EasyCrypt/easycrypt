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

open Stdlib

(** Identifiers *)

(** {2 Labels} *)

type label = string

(** {2 Identifiers} *)

type ident = private {
  id_string : string;               (* non-unique name *)
  id_label  : label list;           (* identifier labels *)
  id_loc    : Loc.position option;  (* optional location *)
  id_tag    : Hashweak.tag;         (* unique magical tag *)
}

module Mid : Map.S with type key = ident
module Sid : Mid.Set
module Hid : Hashtbl.S with type key = ident

val id_equal : ident -> ident -> bool

val id_hash : ident -> int

(* a user-created type of unregistered identifiers *)
type preid

(* register a pre-ident (you should never use this function) *)
val id_register : preid -> ident

(* create a fresh pre-ident *)
val id_fresh : ?label:(label list) -> ?loc:Loc.position -> string -> preid

(* create a localized pre-ident *)
val id_user : ?label:(label list) -> string -> Loc.position -> preid

(* create a duplicate pre-ident *)
val id_clone : ?label:(label list) -> ident -> preid

(* create a derived pre-ident (inherit labels and location) *)
val id_derive : ?label:(label list) -> string -> ident -> preid


(** Unique persistent names for pretty printing *)

type ident_printer

val create_ident_printer :
  ?sanitizer : (string -> string) -> string list -> ident_printer
(** start a new printer with a sanitizing function and a blacklist *)

val id_unique :
  ident_printer -> ?sanitizer : (string -> string) -> ident -> string
(** use ident_printer to generate a unique name for ident
    an optional sanitizer is applied over the printer's sanitizer *)

val string_unique : ident_printer -> string -> string
(** Uniquify string *)

val forget_id : ident_printer -> ident -> unit
(** forget an ident *)

val forget_all : ident_printer -> unit
(** forget all idents *)

val sanitizer : (char -> string) -> (char -> string) -> string -> string
(** generic sanitizer taking a separate encoder for the first letter *)

(** various character encoders *)

val char_to_alpha : char -> string
val char_to_lalpha : char -> string
val char_to_ualpha : char -> string
val char_to_alnum : char -> string
val char_to_alnumus : char -> string

