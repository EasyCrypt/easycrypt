(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2011                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
(*    Guillaume Melquiond                                                 *)
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

val fmla_simpl : Term.term -> Term.term

val simplify_formula :  Task.task Trans.trans
val simplify_formula_and_task :  Task.task list Trans.trans

val fmla_remove_quant : Term.term -> Term.term
(** transforms \exists x. x == y /\ F into F[y/x]
    and \forall x. x <> y \/ F into F[y/x] *)

val fmla_cond_subst: (Term.term -> Term.term -> bool) -> Term.term -> Term.term
(** given a formula [f] containing some equality or disequality [t1] ?= [t2]
    such that [filter t1 t2] (resp [filter t2 t1]) evaluates to true,
    [fmla_subst_cond filter f] performs the substitution [t1] -> [t2]
    (resp [t2] -> [t1]) wherever possible and returns an equivalent formula *)
