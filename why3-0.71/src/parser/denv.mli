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

open Util
open Ty
open Term
open Theory

(** Destructive unification *)

type type_var

val find_type_var : loc:Ptree.loc -> type_var Htv.t -> tvsymbol -> type_var
val create_ty_decl_var : ?loc:Ptree.loc -> user:bool -> tvsymbol -> type_var

type dty

val tyvar : type_var -> dty
val tyapp : tysymbol -> dty list -> dty

type dty_view =
  | Tyvar of type_var
  | Tyapp of tysymbol * dty list

val view_dty : dty -> dty_view

val unify : dty -> dty -> bool

val print_dty : Format.formatter -> dty -> unit

val ty_of_dty : dty -> ty

type ident = Ptree.ident

val create_user_id : Ptree.ident -> Ident.preid

type dpattern = { dp_node : dpattern_node; dp_ty : dty }

and dpattern_node =
  | Pwild
  | Pvar of ident
  | Papp of lsymbol * dpattern list
  | Por of dpattern * dpattern
  | Pas of dpattern * ident

val pattern : vsymbol Mstr.t -> dpattern -> vsymbol Mstr.t * pattern

type dterm = { dt_node : dterm_node; dt_ty : dty }

and dterm_node =
  | Tvar of string
  | Tconst of constant
  | Tapp of lsymbol * dterm list
  | Tif of dfmla * dterm * dterm
  | Tlet of dterm * ident * dterm
  | Tmatch of dterm * (dpattern * dterm) list
  | Tnamed of Ptree.label * dterm
  | Teps of ident * dty * dfmla

and dfmla =
  | Fapp of lsymbol * dterm list
  | Fquant of quant * (ident * dty) list * dtrigger list list * dfmla
  | Fbinop of binop * dfmla * dfmla
  | Fnot of dfmla
  | Ftrue
  | Ffalse
  | Fif of dfmla * dfmla * dfmla
  | Flet of dterm * ident * dfmla
  | Fmatch of dterm * (dpattern * dfmla) list
  | Fnamed of Ptree.label * dfmla
  | Fvar of term

and dtrigger =
  | TRterm of dterm
  | TRfmla of dfmla

val term : vsymbol Mstr.t -> dterm -> term

val fmla : vsymbol Mstr.t -> dfmla -> term

(** Specialization *)

val specialize_ty : loc:Ptree.loc -> type_var Htv.t -> ty -> dty

val specialize_lsymbol : loc:Ptree.loc -> lsymbol -> dty list * dty option

(** exported for programs *)

val tvsymbol_of_type_var : type_var -> tvsymbol
