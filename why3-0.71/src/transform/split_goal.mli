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

val stop_split : Ident.label

val split_pos : Term.term -> Term.term list
(** [split_pos f] returns a list [[g1;..;gk]] such that
 [f] is logically equivalent to [g1 /\ .. /\ gk] *)

val split_neg : Term.term -> Term.term list
(** [split_neg f] returns a list [[g1;..;gk]] such that
 [f] is logically equivalent to [g1 \/ .. \/ gk] *)

val full_split_pos : Term.term -> Term.term list
(** [full_split_pos f] returns a list [[g1;..;gk]] such that
 [f] is logically equivalent to [g1 /\ .. /\ gk] and the length
 of the resulting list can be exponential wrt the size of [f] *)

val full_split_neg : Term.term -> Term.term list
(** [full_split_neg f] returns a list [[g1;..;gk]] such that
 [f] is logically equivalent to [g1 \/ .. \/ gk] and the length
 of the resulting list can be exponential wrt the size of [f] *)

val split_goal : Task.task Trans.tlist
val split_all  : Task.task Trans.tlist

val full_split_goal : Task.task Trans.tlist
val full_split_all  : Task.task Trans.tlist

val split_intro : Task.task Trans.tlist
(** [split_intro] is [split_goal] with skolemization and formula separation *)
