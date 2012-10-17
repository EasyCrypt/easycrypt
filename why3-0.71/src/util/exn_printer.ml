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

type exn_printer = Format.formatter -> exn -> unit

let exn_printers =
  (Stack.create () : (Format.formatter -> exn -> unit) Stack.t)

let register exn_printer = Stack.push exn_printer exn_printers

let () =
  let all_exn_printer fmt exn =
    Format.fprintf fmt "anomaly: %s" (Printexc.to_string exn) in
  register all_exn_printer

exception Exit_loop

let exn_printer fmt exn =
  let test f =
    try
      Format.fprintf fmt "@[%a@]" f exn;
      raise Exit_loop
    with
      | Exit_loop -> raise Exit_loop
      | _ -> ()
  in
  try Stack.iter test exn_printers
  with Exit_loop -> ()

(** For Config *)

let () = register
  (fun fmt exn -> match exn with
    | Config.Dynlink.Error error ->
        Format.fprintf fmt "Dynlink: %s" (Config.Dynlink.error_message error)
    | _ -> raise exn)

