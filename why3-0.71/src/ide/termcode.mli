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

(*
val t_dist : term -> term -> float
  (** returns an heuristic distance between the two given terms. The
      result is always between 0.0 and 1.0. It is guaranteed that if
      the result is 0.0 then the terms are equal modulo alpha *)
*)


(*

  [t_shape t] provides a traversal of the term structure, generally
  in the order root-left-right, except for nodes Tquant and Tbin
  which are traversed in the order right-root-left, so that in "A ->
  B" we see B first, and if "Forall x,A" we see A first

*)


val t_shape_buf : Term.term -> string
  (** returns a shape of the given term *)

(*
val t_shape_list : Term.term -> string list
  (** returns a shape of the given term *)

val pr_shape_list : Format.formatter -> Term.term -> unit
*)

val task_checksum : Task.task -> string
