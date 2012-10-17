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

open Stdlib

(** Logic Declarations *)

open Ident
open Ty
open Term

(** {2 Type declaration} *)

type ty_defn =
  | Tabstract
  | Talgebraic of lsymbol list

type ty_decl = tysymbol * ty_defn

(** {2 Logic symbols declaration} *)

type ls_defn

type logic_decl = lsymbol * ls_defn option

val make_ls_defn : lsymbol -> vsymbol list -> term -> logic_decl

val open_ls_defn : ls_defn -> vsymbol list * term

val open_ls_defn_cb : ls_defn -> vsymbol list * term *
                    (lsymbol -> vsymbol list -> term -> logic_decl)

val ls_defn_axiom : ls_defn -> term

val ls_defn_of_axiom : term -> logic_decl option
(** tries to reconstruct a definition from a defining axiom. Do not apply
    this to recursive definitions: it may successfully build a logic_decl,
    which will fail later because of non-assured termination *)

val check_termination : logic_decl list -> (int list) Mls.t
(** [check_termination ldl] returns a mapping of every logical
    symbol defined in [ldl] to a list of its argument positions
    (numbered from 0) that ensures a lexicographical structural
    descent for every recursive call. Triggers are ignored.
    @raise NoTerminationProof [ls] when no such list is found for [ls] *)

(** {2 Inductive predicate declaration} *)

type prsymbol = private {
  pr_name : ident;
}

module Mpr : Map.S with type key = prsymbol
module Spr : Mpr.Set
module Hpr : Hashtbl.S with type key = prsymbol
module Wpr : Hashweak.S with type key = prsymbol

val create_prsymbol : preid -> prsymbol

val pr_equal : prsymbol -> prsymbol -> bool

val pr_hash : prsymbol -> int

type ind_decl = lsymbol * (prsymbol * term) list

(* Proposition declaration *)

type prop_kind =
  | Plemma    (* prove, use as a premise *)
  | Paxiom    (* do not prove, use as a premise *)
  | Pgoal     (* prove, do not use as a premise *)
  | Pskip     (* do not prove, do not use as a premise *)

type prop_decl = prop_kind * prsymbol * term

(** {2 Declaration type} *)

type decl = private {
  d_node : decl_node;
  d_syms : Sid.t;         (* idents used in declaration *)
  d_news : Sid.t;         (* idents introduced in declaration *)
  d_tag  : Hashweak.tag;  (* unique magical tag *)
}

and decl_node =
  | Dtype  of ty_decl list      (* recursive types *)
  | Dlogic of logic_decl list   (* recursive functions/predicates *)
  | Dind   of ind_decl list     (* inductive predicates *)
  | Dprop  of prop_decl         (* axiom / lemma / goal *)

module Mdecl : Map.S with type key = decl
module Sdecl : Mdecl.Set
module Wdecl : Hashweak.S with type key = decl

val d_equal : decl -> decl -> bool
val d_hash : decl -> int

(** {2 Declaration constructors} *)

val create_ty_decl : ty_decl list -> decl
val create_logic_decl : logic_decl list -> decl
val create_ind_decl : ind_decl list -> decl
val create_prop_decl : prop_kind -> prsymbol -> term -> decl

(* exceptions *)

exception IllegalTypeAlias of tysymbol
exception NonPositiveTypeDecl of tysymbol * lsymbol * ty

exception InvalidIndDecl of lsymbol * prsymbol
exception NonPositiveIndDecl of lsymbol * prsymbol * lsymbol

exception NoTerminationProof of lsymbol
exception BadLogicDecl of lsymbol * lsymbol
exception UnboundVar of vsymbol
exception ClashIdent of ident

exception EmptyDecl
exception EmptyAlgDecl of tysymbol
exception EmptyIndDecl of lsymbol

(** {2 Utilities} *)

val decl_map : (term -> term) -> decl -> decl

val decl_fold : ('a -> term -> 'a) -> 'a -> decl -> 'a

val decl_map_fold : ('a -> term -> 'a * term) -> 'a -> decl -> 'a * decl

module DeclTF : sig

  val decl_map : (term -> term) -> (term -> term) -> decl -> decl

  val decl_fold : ('a -> term -> 'a) -> ('a -> term -> 'a) -> 'a -> decl -> 'a

  val decl_map_fold : ('a -> term -> 'a * term) ->
                      ('a -> term -> 'a * term) -> 'a -> decl -> 'a * decl
end

(** {2 Known identifiers} *)

type known_map = decl Mid.t

val known_id : known_map -> ident -> unit
val known_add_decl : known_map -> decl -> known_map
val merge_known : known_map -> known_map -> known_map

exception KnownIdent of ident
exception UnknownIdent of ident
exception RedeclaredIdent of ident
exception NonExhaustiveCase of pattern list * term
exception NonFoundedTypeDecl of tysymbol

val find_type_definition : known_map -> tysymbol -> ty_defn
val find_constructors : known_map -> tysymbol -> lsymbol list
val find_inductive_cases : known_map -> lsymbol -> (prsymbol * term) list
val find_logic_definition : known_map -> lsymbol -> ls_defn option
val find_prop : known_map -> prsymbol -> term
val find_prop_decl : known_map -> prsymbol -> prop_kind * term

