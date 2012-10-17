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

val compile_match : Task.task Trans.trans

(* a type constructor tagged "enumeration" generates a finite type
   if and only if all of its non-phantom arguments are finite types *)

val meta_enum : Theory.meta (* [MTtysymbol] *)
val meta_phantom : Theory.meta (* [MTtysymbol; MTint] *)

(* tests whether a type is finite given [meta_enum] and [meta_phantom] *)
val is_finite_ty : Ty.Sts.t -> Theory.meta_arg list list -> (Ty.ty -> bool)
