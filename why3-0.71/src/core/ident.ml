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
open Util

(** Labels *)

type label = string

(** Identifiers *)

type ident = {
  id_string : string;               (* non-unique name *)
  id_label  : label list;           (* identifier labels *)
  id_loc    : Loc.position option;  (* optional location *)
  id_tag    : Hashweak.tag;         (* unique magical tag *)
}

module Id = WeakStructMake (struct
  type t = ident
  let tag id = id.id_tag
end)

module Sid = Id.S
module Mid = Id.M
module Hid = Id.H

type preid = ident

let id_equal : ident -> ident -> bool = (==)

let id_hash id = Hashweak.tag_hash id.id_tag

(* constructors *)

let id_register = let r = ref 0 in fun id ->
  { id with id_tag = (incr r; Hashweak.create_tag !r) }

let create_ident name labels loc = {
  id_string = name;
  id_label  = labels;
  id_loc    = loc;
  id_tag    = Hashweak.dummy_tag;
}

let id_fresh ?(label = []) ?loc nm =
  create_ident nm label loc

let id_user ?(label = []) nm loc =
  create_ident nm label (Some loc)

let id_clone ?(label = []) id =
  create_ident id.id_string (label @ id.id_label) id.id_loc

let id_derive ?(label = []) nm id =
  create_ident nm (label @ id.id_label) id.id_loc

(** Unique names for pretty printing *)

type ident_printer = {
  indices   : (string, int) Hashtbl.t;
  values    : string Hid.t;
  sanitizer : string -> string;
  blacklist : string list;
}

let find_unique indices name =
  let specname ind = name ^ string_of_int ind in
  let testname ind = Hashtbl.mem indices (specname ind) in
  let rec advance ind =
    if testname ind then advance (succ ind) else ind in
  let rec retreat ind =
    if ind = 1 || testname (pred ind) then ind else retreat (pred ind) in
  let fetch ind =
    if testname ind then advance (succ ind) else retreat ind in
  let name = try
    let ind = fetch (succ (Hashtbl.find indices name)) in
    Hashtbl.replace indices name ind;
    specname ind
  with Not_found -> name in
  Hashtbl.replace indices name 0;
  name

let reserve indices name = ignore (find_unique indices name)

let same x = x

let create_ident_printer ?(sanitizer = same) sl =
  let indices = Hashtbl.create 1997 in
  List.iter (reserve indices) sl;
  { indices   = indices;
    values    = Hid.create 1997;
    sanitizer = sanitizer;
    blacklist = sl }

let id_unique printer ?(sanitizer = same) id =
  try
    Hid.find printer.values id
  with Not_found ->
    let name = sanitizer (printer.sanitizer id.id_string) in
    let name = find_unique printer.indices name in
    Hid.replace printer.values id name;
    name

let string_unique printer s = find_unique printer.indices s

let forget_id printer id =
  try
    let name = Hid.find printer.values id in
    Hashtbl.remove printer.indices name;
    Hid.remove printer.values id
  with Not_found -> ()

let forget_all printer =
  Hid.clear printer.values;
  Hashtbl.clear printer.indices;
  List.iter (reserve printer.indices) printer.blacklist

(** Sanitizers *)

let unsanitizable = Debug.register_flag "unsanitizable"

let char_to_alpha c = match c with
  | 'a'..'z' | 'A'..'Z' -> String.make 1 c
  | ' ' -> "sp" | '_'  -> "us" | '#' -> "sh"
  | '`' -> "bq" | '~'  -> "tl" | '!' -> "ex"
  | '@' -> "at" | '$'  -> "dl" | '%' -> "pc"
  | '^' -> "cf" | '&'  -> "et" | '*' -> "as"
  | '(' -> "lp" | ')'  -> "rp" | '-' -> "mn"
  | '+' -> "pl" | '='  -> "eq" | '[' -> "lb"
  | ']' -> "rb" | '{'  -> "lc" | '}' -> "rc"
  | ':' -> "cl" | '\'' -> "qt" | '"' -> "dq"
  | '<' -> "ls" | '>'  -> "gt" | '/' -> "sl"
  | '?' -> "qu" | '\\' -> "bs" | '|' -> "br"
  | ';' -> "sc" | ','  -> "cm" | '.' -> "dt"
  | '0' -> "zr" | '1'  -> "un" | '2' -> "du"
  | '3' -> "tr" | '4'  -> "qr" | '5' -> "qn"
  | '6' -> "sx" | '7'  -> "st" | '8' -> "oc"
  | '9' -> "nn" | '\n' -> "br"
  | _ ->
    Debug.dprintf unsanitizable "Unsanitizable : '%c' can't be sanitized@." c;
    "zz"

let char_to_lalpha c = String.uncapitalize (char_to_alpha c)
let char_to_ualpha c = String.capitalize (char_to_alpha c)

let char_to_alnum c =
  match c with '0'..'9' -> String.make 1 c | _ -> char_to_alpha c

let char_to_alnumus c =
  match c with '_' | ' ' -> "_" | _ -> char_to_alnum c

let sanitizer head rest n =
  let lst = ref [] in
  let code c = lst := rest c :: !lst in
  let n = if n = "" then "zilch" else n in
  String.iter code n;
  let rst = List.tl (List.rev !lst) in
  let cs = head (String.get n 0) :: rst in
  String.concat "" cs
