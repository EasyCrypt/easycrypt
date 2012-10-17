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

open Ty
open Term
open Decl

val debug : Debug.flag

(* meta to tag the protected types *)
val meta_kept : Theory.meta

(* sort symbol of the "universal" type *)
val ts_base : tysymbol

(* "universal" sort *)
val ty_base : ty

(* ts_base type declaration *)
val d_ts_base : decl

(* sort symbol of (polymorphic) types *)
val ts_type : tysymbol

(* sort of (polymorphic) types *)
val ty_type : ty

(* ts_type declaration *)
val d_ts_type : decl

(* function symbol mapping ty_type^n to ty_type *)
val ls_of_ts : tysymbol -> lsymbol

(* function symbol mapping ty_type^n to int *)
val ls_int_of_ty : lsymbol

(* function symbol selecting ty_type from ty_type^n *)
val ls_selects_of_ts : tysymbol -> lsymbol list

(* convert a type to a term of type ty_type *)
val term_of_ty : term Mtv.t -> ty -> term

(* rewrite a closed formula modulo the given free typevars *)
val type_close : Stv.t -> (term Mtv.t -> 'a -> term) -> 'a -> term

(* rewrite a closed formula modulo its free typevars *)
val t_type_close : (term Mtv.t -> term -> term) -> term -> term

(* convert a type declaration to a list of lsymbol declarations *)
val lsdecl_of_tydecl : ty_decl list -> decl list

(* convert a type declaration to a list of lsymbol declarations *)
val lsdecl_of_tydecl_select : ty_decl list -> decl list

(* a pre-id for vsymbols and lsymbols that produce non-kept values *)
val id_unprotected : string -> Ident.preid
val is_protected_id : Ident.ident -> bool

(* a pre-id for lsymbols that treat their arguments as non-kept *)
val id_unprotecting : string -> Ident.preid
val is_protecting_id : Ident.ident -> bool

(* the value type is in kept and the ident is not unprotected *)
val is_protected_vs : Sty.t -> vsymbol -> bool
val is_protected_ls : Sty.t -> lsymbol -> bool

(* monomorphise wrt the set of kept types, and a symbol map *)
val d_monomorph : Sty.t -> (lsymbol -> lsymbol) -> decl -> decl list

(* replace type variables in a goal with fresh type constants *)
val monomorphise_goal : Task.task Trans.trans

(* close by subtype the set of types tagged by meta_kept *)
val close_kept : Task.task Trans.trans

(* reconstruct a definition of an lsymbol or make a defining axiom *)
val defn_or_axiom : lsymbol -> term -> decl list

