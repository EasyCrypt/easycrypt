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

{
open Lexing
open Format
open Util

let get_home_dir () =
  try Sys.getenv "HOME"
  with Not_found ->
    (* try windows env var *)
    try Sys.getenv "USERPROFILE"
    with Not_found -> ""

type rc_value =
  | RCint of int
  | RCbool of bool
  | RCfloat of float
  | RCstring of string
  | RCident of string


(* Error handling *)

(* exception SyntaxError *)
exception ExtraParameters of string
exception MissingParameters of string
(* exception UnknownSection of string *)
exception UnknownField of string
(* exception MissingSection of string *)
exception MissingField of string
exception DuplicateSection of string
exception DuplicateField of string * rc_value * rc_value
exception StringExpected of string * rc_value
exception IdentExpected of string * rc_value
exception IntExpected of string * rc_value
exception BoolExpected of string * rc_value

let error ?loc e = match loc with
  | None -> raise e
  | Some loc -> raise (Loc.Located (loc, e))

(* conf files *)

let print_rc_value fmt = function
  | RCint i -> fprintf fmt "%d" i
  | RCbool b -> fprintf fmt "%B" b
  | RCfloat f -> fprintf fmt "%f" f
  | RCstring s -> fprintf fmt "%S" s (* "%s"  %S ? *)
  | RCident s -> fprintf fmt "%s" s

let () = Exn_printer.register (fun fmt e -> match e with
  (* | SyntaxError -> *)
  (*     fprintf fmt "syntax error" *)
  | ExtraParameters s ->
      fprintf fmt "section '%s': header too long" s
  | MissingParameters s ->
      fprintf fmt "section '%s': header too short" s
  (* | UnknownSection s -> *)
  (*     fprintf fmt "unknown section '%s'" s *)
  | UnknownField s ->
      fprintf fmt "unknown field '%s'" s
  (* | MissingSection s -> *)
  (*     fprintf fmt "section '%s' is missing" s *)
  | MissingField s ->
      fprintf fmt "field '%s' is missing" s
  | DuplicateSection s ->
      fprintf fmt "section '%s' is already given" s
  | DuplicateField (s,u,v) ->
      fprintf fmt "cannot set field '%s' to %a, as it is already set to %a"
        s print_rc_value v print_rc_value u
  | StringExpected (s,v) ->
      fprintf fmt "cannot set field '%s' to %a: a string is expected"
        s print_rc_value v
  | IdentExpected (s,v) ->
      fprintf fmt "cannot set field '%s' to %a: an identifier is expected"
        s print_rc_value v
  | IntExpected (s,v) ->
      fprintf fmt "cannot set field '%s' to %a: an integer is expected"
        s print_rc_value v
  | e -> raise e)

type section = rc_value list Mstr.t
type family  = (string * section) list
type ofamily  = (string option * section) list
type t = ofamily Mstr.t

let empty = Mstr.empty
let empty_section = Mstr.empty

let make_t tl =
  let add_key acc (key,value) =
    let l = Mstr.find_default key [] acc in
    Mstr.add key (value::l) acc in
  let add_section t (args,sectionl) =
    let sname,arg = match args with
      | []    -> assert false
      | [sname]    -> sname,None
      | [sname;arg] -> sname,Some arg
      | sname::_     -> raise (ExtraParameters sname) in
    let m = List.fold_left add_key empty_section sectionl in
    let m = Mstr.map List.rev m in
    let l = Mstr.find_default sname [] t in
    Mstr.add sname ((arg,m)::l) t in
  List.fold_left add_section empty tl

let get_section t sname =
  try
    let l = Mstr.find sname t in
    match l with
      | [None,v] -> Some v
      | [Some _,_] -> raise (ExtraParameters sname)
      | _ -> raise (DuplicateSection sname)
  with Not_found -> None

let get_family t sname =
  try
    let l = Mstr.find sname t in
    let get (arg,section) =
      (match arg with None -> raise (MissingParameters sname) | Some v -> v,
        section) in
    List.map get l
  with Not_found -> []


let set_section t sname section =
  Mstr.add sname [None,section] t

let set_family t sname sections =
  if sections = [] then Mstr.remove sname t else
    let set (arg,section) = (Some arg,section) in
    Mstr.add sname (List.map set sections) t

let get_value read section key =
  let l = Mstr.find key section in
  match l with
    | []  -> assert false
    | [v] -> read key v
    | v1::v2::_ -> raise (DuplicateField (key,v1,v2))

let get_value read ?default section key =
  try
    get_value read section key
  with Not_found ->
    match default with
      | None -> raise (MissingField key)
      | Some v -> v

let get_valueo read section key =
  try
    Some (get_value read section key)
  with MissingField _ -> None

let get_valuel read ?default section key =
  try
    let l = Mstr.find key section in
    List.map (read key) l
  with Not_found ->
    match default with
      | None -> raise (MissingField key)
      | Some v -> v

let set_value write ?default section key value =
  let actually_write = match default with
    | None -> true
    | Some default -> default <> value in
  if actually_write
  then Mstr.add key [write value] section
  else section

let set_valuel write ?default section key valuel =
  if valuel = [] then Mstr.remove key section else
    let actually_write = match default with
      | None -> true
      | Some default -> default <> valuel in
    if actually_write
    then Mstr.add key (List.map write valuel) section
    else Mstr.remove key section

let rint k = function
  | RCint n -> n
  | v -> raise (IntExpected (k,v))

let wint i = RCint i

let rbool k = function
  | RCbool b -> b
  | v -> raise (BoolExpected (k,v))

let wbool b = RCbool b

let rstring k = function
  | RCident s | RCstring s -> s
  | v -> raise (StringExpected (k,v))

let wstring s = RCstring s

let get_int = get_value rint
let get_intl = get_valuel rint
let get_into = get_valueo rint

let set_int = set_value wint
let set_intl = set_valuel wint

let get_bool = get_value rbool
let get_booll = get_valuel rbool
let get_boolo = get_valueo rbool
let set_bool = set_value wbool
let set_booll = set_valuel wbool

let get_string = get_value rstring
let get_stringl = get_valuel rstring
let get_stringo = get_valueo rstring
let set_string = set_value wstring
let set_stringl = set_valuel wstring

let check_exhaustive section keyl =
  let test k _ = if Sstr.mem k keyl then ()
    else raise (UnknownField k) in
  Mstr.iter test section

let buf = Buffer.create 17

let current_rec = ref []
let current_list = ref []
let current = ref []

let push_field key value =
  current_list := (key,value) :: !current_list

let push_record () =
  if !current_list <> [] then
    current := (!current_rec,List.rev !current_list) :: !current;
  current_rec := [];
  current_list := []

  exception SyntaxError of string
  let syntax_error s = raise (SyntaxError s)

}

let space = [' ' '\t' '\r' '\n']+
let digit = ['0'-'9']
let letter = ['a'-'z' 'A'-'Z']
let ident = (letter | '_') (letter | digit | '_' | '-' | '+' | '.') *
let sign = '-' | '+'
let integer = sign? digit+
let mantissa = ['e''E'] sign? digit+
let real = sign? digit* '.' digit* mantissa?
let escape = ['\\''"''n''t''r']

rule record = parse
  | space
      { record lexbuf }
  | '#' [^'\n']* ('\n' | eof)
      { record lexbuf }
  | '[' (ident as key) space*
      { header [key] lexbuf }
  | eof
      { push_record () }
  | (ident as key) space* '=' space*
      { value key lexbuf }
  | _ as c
      { syntax_error ("invalid keyval pair starting with " ^ String.make 1 c) }

and header keylist = parse
  | (ident as key) space*
      { header (key::keylist) lexbuf }
  | ']'
      { push_record ();
        current_rec := List.rev keylist;
        record lexbuf }
  | eof
      { syntax_error "unterminated header" }
  | _ as c
      { syntax_error ("invalid header starting with " ^ String.make 1 c) }

and value key = parse
  | integer as i
      { push_field key (RCint (int_of_string i));
        record lexbuf }
  | real as r
      { push_field key (RCfloat (float_of_string r));
        record lexbuf }
  | '"'
      { Buffer.clear buf;
        string_val key lexbuf }
  | "true"
      { push_field key (RCbool true);
        record lexbuf }
  | "false"
      { push_field key (RCbool false);
        record lexbuf }
  | ident as id
      { push_field key (RCident (*kind_of_ident*) id);
        record lexbuf }
  | eof
      { syntax_error "unterminated keyval pair" }
  | _ as c
      { syntax_error ("invalid value starting with " ^ String.make 1 c) }

and string_val key = parse
  | '"'
      { push_field key (RCstring (Buffer.contents buf));
        record lexbuf
      }
  | [^ '\\' '"'] as c
      { Buffer.add_char buf c;
        string_val key lexbuf }
  | '\\' (['\\''\"'] as c)
      { Buffer.add_char buf c;
        string_val key lexbuf }
  | '\\' 'n'
      { Buffer.add_char buf '\n';
        string_val key lexbuf }
  | '\\' '\n'
      { string_val key lexbuf }
  | '\\' (_ as c)
      { Buffer.add_char buf '\\';
        Buffer.add_char buf c;
        string_val key lexbuf }
  | eof
      { syntax_error "unterminated string" }


{

let from_channel cin =
  current := [];
  record (from_channel cin);
  make_t !current

exception CannotOpen of string * string
exception SyntaxErrorFile of string * string

let from_file f =
  let c =
    try open_in f with Sys_error s -> raise (CannotOpen (f, s))
  in
  try
    let r = from_channel c in close_in c; r
  with
    | SyntaxError s -> close_in c; raise (SyntaxErrorFile (f, s))
    | e -> close_in c; raise e

let () = Exn_printer.register (fun fmt e -> match e with
  | CannotOpen (_, s) ->
      Format.fprintf fmt "system error: `%s'" s
  | SyntaxErrorFile (f, s) ->
      Format.fprintf fmt "syntax error in %s: %s" f s
  | _ -> raise e)

let to_formatter fmt t =
  let print_kv k fmt v = fprintf fmt "%s = %a" k print_rc_value v in
  let print_kvl fmt k vl = Pp.print_list Pp.newline (print_kv k) fmt vl in
  let print_section sname fmt (h,l) =
    fprintf fmt "[%s %a]@\n%a"
      sname (Pp.print_option Pp.string) h
      (Pp.print_iter22 Mstr.iter Pp.newline print_kvl) l in
  let print_sectionl fmt sname l =
    Pp.print_list Pp.newline2 (print_section sname) fmt l in
  let print_t fmt t =
    Pp.print_iter22 Mstr.iter Pp.newline2 print_sectionl fmt t in
  print_t fmt t;
  pp_print_newline fmt ()

let to_channel cout t =
  to_formatter (formatter_of_out_channel cout) t

let to_file s t =
  let out = open_out s in
  to_channel out t;
  close_out out

}
