(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2011                                               *)
(*    François Bobot                                                      *)
(*    Simon Cruanes                                                       *)
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

(** abstract tree representation *)

type atom = string
type variable = string


type logical_binop = And | Or | Implies | Equiv
type logical_unop = Not
type term_binop = Equal | NotEqual
type quantifier = Forall | Exist

type fmla =
  | FBinop of logical_binop * fmla * fmla
  | FUnop of logical_unop * fmla
  | FQuant of quantifier * variable list * fmla
  | FPred of predicate * term list
  | FTermBinop of term_binop * term * term
and term =
  | TAtom of atom
  | TConst of string
  | TVar of variable
  | TFunctor of atom * term list
and predicate = string


(** a tptp declaration *)
type decl =
| Fof of string * declType * fmla
| Cnf of string * declType * fmla
| Include of string
and declType = Axiom | Conjecture | NegatedConjecture | Lemma

type tptp = decl list
