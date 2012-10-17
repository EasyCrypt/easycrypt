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

(*i $Id: pp.ml,v 1.22 2009-10-19 11:55:33 bobot Exp $ i*)

(*s Pretty-print library *)

open Format

let print_option f fmt = function
  | None -> ()
  | Some x -> f fmt x

let print_option_or_default default f fmt = function
  | None -> fprintf fmt "%s" default
  | Some x -> f fmt x

let rec print_list sep print fmt = function
  | [] -> ()
  | [x] -> print fmt x
  | x :: r -> print fmt x; sep fmt (); print_list sep print fmt r

let print_list_or_default default sep print fmt = function
  | [] -> fprintf fmt "%s" default
  | l -> print_list sep print fmt l

let print_list_par sep pr fmt l =
  print_list sep (fun fmt x -> fprintf fmt "(%a)" pr x) fmt l

let print_list_delim start stop sep pr fmt = function
  | [] -> ()
  | l -> fprintf fmt "%a%a%a" start () (print_list sep pr) l stop ()


let print_iter1 iter sep print fmt l =
  let first = ref true in
  iter (fun x ->
          if !first
          then first := false
          else sep fmt ();
          print fmt x ) l

let print_iter2 iter sep1 sep2 print1 print2 fmt l =
  let first = ref true in
  iter (fun x y ->
          if !first
          then first := false
          else sep1 fmt ();
          print1 fmt x;sep2 fmt (); print2 fmt y) l


let print_iter22 iter sep print fmt l =
  let first = ref true in
  iter (fun x y ->
          if !first
          then first := false
          else sep fmt ();
          print fmt x y) l


let print_pair_delim start sep stop pr1 pr2 fmt (a,b) =
  fprintf fmt "%a%a%a%a%a" start () pr1 a sep () pr2 b stop ()

let dot fmt () = fprintf fmt ".@ "
let comma fmt () = fprintf fmt ",@ "
let star fmt () = fprintf fmt "*@ "
let simple_comma fmt () = fprintf fmt ", "
let underscore fmt () = fprintf fmt "_"
let semi fmt () = fprintf fmt ";@ "
let space fmt () = fprintf fmt "@ "
let alt fmt () = fprintf fmt "|@ "
let equal fmt () = fprintf fmt "@ =@ "
let newline fmt () = fprintf fmt "@\n"
let newline2 fmt () = fprintf fmt "@\n@\n"
let arrow fmt () = fprintf fmt "@ -> "
let lbrace fmt () = fprintf fmt "{"
let rbrace fmt () = fprintf fmt "}"
let lsquare fmt () = fprintf fmt "["
let rsquare fmt () = fprintf fmt "]"
let lparen fmt () = fprintf fmt "("
let rparen fmt () = fprintf fmt ")"
let lchevron fmt () = fprintf fmt "<"
let rchevron fmt () = fprintf fmt ">"
let nothing _fmt _ = ()
let string fmt s = fprintf fmt "%s" s
let constant_string s fmt () = string fmt s
let add_flush sep fmt x = sep fmt x; pp_print_flush fmt ()

let print_pair pr1 = print_pair_delim lparen comma rparen pr1

let hov n fmt f x = pp_open_hovbox fmt n; f x; pp_close_box fmt ()

let open_formatter ?(margin=78) cout =
  let fmt = formatter_of_out_channel cout in
  pp_set_margin fmt margin;
  pp_open_box fmt 0;
  fmt

let close_formatter fmt =
  pp_close_box fmt ();
  pp_print_flush fmt ()

let open_file_and_formatter ?(margin=78) f =
  let cout = open_out f in
  let fmt = open_formatter ~margin cout in
  cout,fmt

let close_file_and_formatter (cout,fmt) =
  close_formatter fmt;
  close_out cout

let print_in_file_no_close ?(margin=78) p f =
  let cout,fmt = open_file_and_formatter ~margin f in
  p fmt;
  close_formatter fmt;
  cout

let print_in_file ?(margin=78) p f =
  let cout = print_in_file_no_close ~margin p f in
  close_out cout



(* With optional separation *)
let rec print_list_opt sep print fmt = function
  | [] -> false
  | [x] -> print fmt x
  | x :: r ->
      let notempty1 = print fmt x in
      if notempty1 then sep fmt ();
      let notempty2 = print_list_opt sep print fmt r in
      notempty1 || notempty2


let string_of p x =
  let b = Buffer.create 100 in
  let fmt = formatter_of_buffer b in
  fprintf fmt "%a@?" p x;
  Buffer.contents b

let wnl fmt =
  let out,flush,_newline,spaces =
    pp_get_all_formatter_output_functions fmt () in
  pp_set_all_formatter_output_functions fmt
    ~out ~flush ~newline:(fun () -> spaces 1) ~spaces


let string_of_wnl p x =
  let b = Buffer.create 100 in
  let fmt = formatter_of_buffer b in
  wnl fmt;
  fprintf fmt "%a@?" p x;
  Buffer.contents b

module Ansi =
  struct

    let set_column fmt n = fprintf fmt "\027[%iG" n
end
