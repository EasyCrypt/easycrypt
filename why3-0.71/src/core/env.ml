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

open Util
open Ident
open Theory

(** Library environment *)

type fformat = string (* format name *)
type filename = string (* file name *)
type extension = string (* file extension *)
type pathname = string list (* path in an environment *)

exception KnownFormat of fformat
exception UnknownFormat of fformat
exception UnknownExtension of extension
exception UnspecifiedFormat

exception ChannelNotFound of pathname
exception TheoryNotFound of pathname * string
exception AmbiguousPath of filename * filename

type env = {
  env_path : filename list;
  env_memo : (pathname, theory Mstr.t) Hashtbl.t;
  env_tag  : Hashweak.tag;
}

let env_tag env = env.env_tag

module Wenv = Hashweak.Make(struct type t = env let tag = env_tag end)

(** Input formats *)

type read_channel =
  env -> pathname -> filename -> in_channel -> theory Mstr.t

let read_channel_table = Hashtbl.create 17 (* format name -> read_channel *)
let extensions_table   = Hashtbl.create 17 (* suffix -> format name *)

let register_format name exts rc =
  if Hashtbl.mem read_channel_table name then raise (KnownFormat name);
  Hashtbl.add read_channel_table name (rc,exts);
  List.iter (fun s -> Hashtbl.replace extensions_table ("." ^ s) name) exts

let lookup_format name =
  try Hashtbl.find read_channel_table name
  with Not_found -> raise (UnknownFormat name)

let get_extension file =
  let s = try Filename.chop_extension file
    with Invalid_argument _ -> raise UnspecifiedFormat in
  let n = String.length s in
  String.sub file n (String.length file - n)

let get_format file =
  let ext = get_extension file in
  try Hashtbl.find extensions_table ext
  with Not_found -> raise (UnknownExtension ext)

let real_read_channel ?format env path file ic =
  let name = match format with
    | Some name -> name
    | None -> get_format file in
  let rc,_ = lookup_format name in
  rc env path file ic

let read_channel ?format env file ic =
  real_read_channel ?format env [] file ic

let read_file ?format env file =
  let ic = open_in file in
  try
    let mth = read_channel ?format env file ic in
    close_in ic;
    mth
  with e -> close_in ic; raise e

let list_formats () =
  let add n (_,l) acc = (n,l)::acc in
  Hashtbl.fold add read_channel_table []


(** Environment construction and utilisation *)

let create_env = let c = ref (-1) in fun lp -> {
  env_path = lp;
  env_memo = Hashtbl.create 17;
  env_tag  = (incr c; Hashweak.create_tag !c)
}

let create_env_of_loadpath lp =
  Format.eprintf "WARNING: Env.create_env_of_loadpath is deprecated
    and will be removed in future versions of Why3.
    Replace it with Env.create_env.@.";
  create_env lp

let get_loadpath env = env.env_path

(* looks for file [file] of format [name] in loadpath [lp] *)
let locate_file name lp path =
  let file = List.fold_left Filename.concat "" path in
  let _,sl = lookup_format name in
  let add_sf sf = file ^ "." ^ sf in
  let fl = if sl = [] then [file] else List.map add_sf sl in
  let add_dir dir = List.map (Filename.concat dir) fl in
  let fl = List.concat (List.map add_dir lp) in
  match List.filter Sys.file_exists fl with
  | [] -> raise (ChannelNotFound path)
  | [file] -> file
  | file1 :: file2 :: _ -> raise (AmbiguousPath (file1, file2))

exception InvalidQualifier of string

let check_qualifier s =
  let find_dir_sep s =
    let re = Str.regexp_string Filename.dir_sep in
    try ignore (Str.search_forward re s 0); true
    with Not_found -> false in
  if (s = Filename.parent_dir_name ||
      s = Filename.current_dir_name ||
      find_dir_sep s)
  then raise (InvalidQualifier s)

let find_channel env f sl =
  List.iter check_qualifier sl;
  let file = locate_file f env.env_path sl in
  file, open_in file

let find_library env sl =
  let file, ic = find_channel env "why" sl in
  try
    Hashtbl.replace env.env_memo sl Mstr.empty;
    let mth = real_read_channel ~format:"why" env sl file ic in
    Hashtbl.replace env.env_memo sl mth;
    close_in ic;
    mth
  with e ->
    Hashtbl.remove env.env_memo sl;
    close_in ic;
    raise e

let find_library env sl =
  try Hashtbl.find env.env_memo sl
  with Not_found -> find_library env sl

let get_builtin s =
  if s = builtin_theory.th_name.id_string then builtin_theory else
  if s = highord_theory.th_name.id_string then highord_theory else
  match tuple_theory_name s with
  | Some n -> tuple_theory n
  | None -> raise (TheoryNotFound ([],s))

let find_theory env sl s =
  if sl = [] then get_builtin s else
  let mth = find_library env sl in
  try Mstr.find s mth with Not_found ->
  raise (TheoryNotFound (sl,s))

(* Exception reporting *)

let () = Exn_printer.register
  begin fun fmt exn -> match exn with
  | ChannelNotFound sl ->
      Format.fprintf fmt "Library not found: %a"
        (Pp.print_list (Pp.constant_string ".") Format.pp_print_string) sl
  | TheoryNotFound (sl,s) ->
      Format.fprintf fmt "Theory not found: %a.%s"
        (Pp.print_list (Pp.constant_string ".") Format.pp_print_string) sl s
  | KnownFormat s ->
      Format.fprintf fmt "Format %s is already registered" s
  | UnknownFormat s ->
      Format.fprintf fmt "Unknown input format: %s" s
  | UnknownExtension s ->
      Format.fprintf fmt "Unknown file extension: `%s'" s
  | UnspecifiedFormat ->
      Format.fprintf fmt "Format not specified"
  | AmbiguousPath (f1,f2) ->
      Format.fprintf fmt "Ambiguous path:@ both `%s'@ and `%s'@ match" f1 f2
  | InvalidQualifier s ->
      Format.fprintf fmt "Invalid qualifier `%s'" s
  | _ -> raise exn
  end

