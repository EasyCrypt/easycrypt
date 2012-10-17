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

(** Inline non-recursive definitions *)

val meta : Theory.meta

(** {2 Generic inlining} *)

val t :
  ?use_meta:bool ->
  ?in_goal:bool ->
  notdeft:(Term.term -> bool) ->
  notdeff:(Term.term -> bool) ->
  notls  :(Term.lsymbol -> bool) ->
  Task.task Trans.trans

(** [t ~use_meta ~in_goal ~notdeft ~notdeff ~notls] returns a transformation
    that expands a symbol [ls] in the subsequent declarations unless [ls]
    satisfies one of the following conditions:
    - [ls] is defined via a (mutually) recursive definition;
    - [ls] is an inductive predicate or an algebraic type constructor;
    - [ls] is a function symbol and [notdeft] returns true on its definition;
    - [ls] is a predicate symbol and [notdeff] returns true on its definition;
    - [notls ls] returns [true];
    - [use_meta] is set and [ls] is tagged by "inline : no"

    Notice that [use_meta], [notdeft], [notdeff], [notls] restrict only which
    symbols are inlined not when.

    If [in_goal] is set, only the top-most symbols in the goal are expanded.
*)

(** {2 Registered Transformation} *)

val all : Task.task Trans.trans
(** [all] corresponds to the transformation "inline_all" *)

val goal : Task.task Trans.trans
(** [goal] corresponds to the transformation "inline_goal" *)

val trivial : Task.task Trans.trans
(** [trivial] corresponds to the transformation "inline_trivial"
    Inline only the trivial definition :
    logic c : t = a
    logic f(x : t,...., ) : t = g(y : t2,...) *)

(*
(** Functions to use in other transformations if inlining is needed *)

type env

val empty_env : env

val addfs : env -> Term.lsymbol -> Term.vsymbol list -> Term.term -> env
val addps : env -> Term.lsymbol -> Term.vsymbol list -> Term.term -> env
(** [addls env ls vs t] trigger the inlining of [ls] by the definition
    [t] with the free variables [vs]. The variables of [vs] must have
    the same type as the arguments of [ls] *)

val replacet : env -> Term.term -> Term.term
val replacep : env -> Term.term -> Term.term
*)
