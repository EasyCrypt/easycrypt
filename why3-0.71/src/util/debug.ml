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

let formatter = ref Format.err_formatter

exception UnknownFlag of string

type flag = bool ref

let flag_table = Hashtbl.create 17

let register_flag s =
  try
    Hashtbl.find flag_table s
  with Not_found ->
    let flag = ref false in
    Hashtbl.replace flag_table s flag;
    flag

let lookup_flag s =
  try Hashtbl.find flag_table s with Not_found -> raise (UnknownFlag s)

let list_flags () = Hashtbl.fold (fun s v acc -> (s,v,!v)::acc) flag_table []

let test_flag s = !s
let nottest_flag s = not !s

let set_flag s = s := true
let unset_flag s = s := false
let toggle_flag s = s := not !s

let () = Exn_printer.register (fun fmt e -> match e with
  | UnknownFlag s -> Format.fprintf fmt "unknown debug flag `%s'@." s
  | _ -> raise e)

let stack_trace = register_flag "stack_trace"
let timestamp = register_flag "timestamp"
let time_start = Unix.gettimeofday ()

let set_debug_formatter = (:=) formatter
let get_debug_formatter () = !formatter

let dprintf flag s =
  if !flag then
    begin
      if !timestamp then Format.fprintf !formatter "<%f>"
        (Unix.gettimeofday () -. time_start);
      Format.fprintf !formatter s
    end
  else Format.ifprintf !formatter s
