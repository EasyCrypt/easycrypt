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

(* Compilation of pattern-matching *)

open Ty
open Term

module type Action = sig
  type action
  type branch
  val mk_let : vsymbol -> term -> action -> action
  val mk_branch : pattern -> action -> branch
  val mk_case : term -> branch list -> action
end

exception ConstructorExpected of lsymbol
exception NonExhaustive of pattern list

module Compile (X : Action) : sig
  val compile : (tysymbol -> lsymbol list) ->
    term list -> (pattern list * X.action) list -> X.action
end

module CompileTerm : sig
  val compile : (tysymbol -> lsymbol list) ->
    term list -> (pattern list * term) list -> term
end
