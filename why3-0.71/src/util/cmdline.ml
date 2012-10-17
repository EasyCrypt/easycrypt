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

exception BadEscape of string * char
exception UnfinishedEscape of string
exception UnclosedQuote of string
exception UnclosedDQuote of string
exception EmptyCommandLine

let is_blank = function
  | ' ' | '\t' | '\n' | '\r' -> true
  | _ -> false

let escape s c = match c with
  | 't' -> '\t' | 'n' -> '\n' | 'r' -> '\r'
  | '\'' | '"' | '\\' | ' ' -> c
  | _ -> raise (BadEscape (s,c))

type fsm_state =
  | Normal
  | Blank
  | Quote
  | DQuote
  | Escape
  | QEscape
  | DQEscape

let cmdline_split s =
  let argv = ref [] in
  let cur_arg = Queue.create () in
  let cstate = ref Blank in
  let normal = function
    | '\'' -> cstate := Quote
    | '"' -> cstate := DQuote
    | '\\' -> cstate := Escape
    | c when is_blank c ->
        let n = Queue.length cur_arg in
        let s = String.create n in
        for i = 0 to pred n do
          String.set s i (Queue.take cur_arg)
        done;
        argv := s :: !argv;
        cstate := Blank
    | c -> Queue.add c cur_arg
  in
  let blank = function
    | '\'' -> cstate := Quote
    | '"' -> cstate := DQuote
    | '\\' -> cstate := Escape
    | c when is_blank c -> ()
    | c -> Queue.add c cur_arg; cstate := Normal
  in
  let quote = function
    | '\'' -> cstate := Normal
    | '\\' -> cstate := QEscape
    | c -> Queue.add c cur_arg
  in
  let dquote = function
    | '"' -> cstate := Normal
    | '\\' -> cstate := DQEscape
    | c -> Queue.add c cur_arg
  in
  let fsm c = match !cstate with
    | Normal -> normal c
    | Blank -> blank c
    | Quote -> quote c
    | DQuote -> dquote c
    | Escape -> Queue.add (escape s c) cur_arg; cstate := Normal
    | QEscape -> Queue.add (escape s c) cur_arg; cstate := Quote
    | DQEscape -> Queue.add (escape s c) cur_arg; cstate := DQuote
  in
  String.iter fsm s;
  fsm ' ';
  match !cstate with
    | Normal ->
        assert false
    | Blank ->
        if !argv = [] then raise EmptyCommandLine else
        List.rev !argv
    | Quote ->
        raise (UnclosedQuote s)
    | DQuote ->
        raise (UnclosedDQuote s)
    | Escape | QEscape | DQEscape ->
        raise (UnfinishedEscape s)

let () = Exn_printer.register (fun fmt e -> match e with
  | BadEscape (s,c) ->
      Format.fprintf fmt "bad escape sequence '\\%c' in string: %s" c s
  | UnfinishedEscape s ->
      Format.fprintf fmt "unfinished escape sequence in string: %s" s
  | UnclosedQuote s ->
      Format.fprintf fmt "unclosed quote in string: %s" s
  | UnclosedDQuote s ->
      Format.fprintf fmt "unclosed double quote in string: %s" s
  | EmptyCommandLine ->
      Format.fprintf fmt "empty command line"
  | _ -> raise e)

