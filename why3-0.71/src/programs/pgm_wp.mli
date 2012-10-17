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

open Why3
open Term

val debug : Debug.flag

val decl : Pgm_module.uc -> Pgm_ttree.decl -> Pgm_module.uc
  (** weakest preconditions: takes a module (under construction) as argument,
      and a program declaration, and adds the verification conditions for that
      declaration as goals (in the logic theory contained in the module). *)

val declare_global_regions : Pgm_types.T.pvsymbol -> unit

val declare_mutable_field : Ty.tysymbol -> int -> int -> unit
  (* [declare_mutable_field ts i j] indicates that region [i] in
     [ts] args correspond to the mutable field [j] of [ts] *)

val default_variant : lsymbol -> lsymbol -> term -> term -> term
  (* [default_variant le lt phi phi0] = 0 <= phi0 and phi < phi0 *)

