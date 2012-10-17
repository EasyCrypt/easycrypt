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
(* an [exn_printer] is a formatter of exception which prints on the
   given formatter a message for the user if it knows the given
   exception. Otherwise it raises the exception *)

val register : exn_printer -> unit
(* Register a formatter of exception *)

val exn_printer : exn_printer
(* exn_printer fmt exn : print the exception using all the previously
   registered printer and return *)
