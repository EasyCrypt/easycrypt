(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2011                                               *)
(*    François Bobot                                                      *)
(*    Simon Cruanes                                                       *)
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

(** this is a parser for tptp problems (.p files) *)

open TptpTree

open Why3

open Lexing

open TptpTranslate


(** module to process a single file *)
module Process : sig

  val read_channel : Env.read_channel

end = struct

  let fromInclude = function | Include x -> x | _ -> assert false
  let isInclude = function | Include _ -> true | _ -> false

  (** for a given file, returns the list of declarations
  for this file and all the files it includes, recursively *)
  let rec getAllDecls ?first:(first=false) include_dir filename =
    try
      let filename = if first then filename else include_dir^"/"^filename in
      let input = if filename = "-" then stdin else open_in filename in
      let decls = myparse input in
      close_in input;
      process_recursively ~include_dir:include_dir decls
    with (Sys_error _) as e ->
      print_endline ("error : unable to open "^filename);
      raise e
  (** read completely a channel *)
  and getDeclsFromChan input =
    let decls = myparse input in
    process_recursively decls
  (** search a list of declarations for include statements *)
  and process_recursively ?(include_dir=".") decls =
    let (to_include, real_decl) = List.partition isInclude decls in
    let to_include = List.map fromInclude to_include in (* remove Include *)
    let all_decls = List.concat
      (List.map (getAllDecls include_dir) to_include) in
    all_decls @ real_decl

  (** parses a single file *)
  and myparse chan =
    let lb = Lexing.from_channel chan in
    TptpParser.tptp TptpLexer.token lb


  let read_channel _env path file c =
    let decls = getDeclsFromChan c in
    if Debug.test_flag Typing.debug_parse_only ||
       Debug.test_flag Typing.debug_type_only
    then Util.Mstr.empty
    else
      let my_theory = theory_of_decls path file decls in
      Util.Mstr.add "Tptp" my_theory Util.Mstr.empty

end

(** register as a .p/.ax file parser *)
let () = Env.register_format "tptp" ["p"] Process.read_channel


(*
Local Variables:
compile-command: "unset LANG; make -C ../.."
End:
*)
