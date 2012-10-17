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

(** Introduction of premises *)

(** The premises of the goal of a task are introduced in the
    context, e.g

      goal G: forall x:t, f1 -> forall y:u, f2 and f3 -> f4

    becomes

      logic x:t
      axiom H1: f1
      logic y:u
      axiom H2: f2
      axiom H3: f3
      goal G: f4

*)

val intros :  Decl.prsymbol -> Term.term -> Decl.decl list
 (** [intros G f] returns the declarations after introducing
     premises of [goal G : f] *)
