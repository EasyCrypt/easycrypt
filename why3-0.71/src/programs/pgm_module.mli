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
open Ident
open Ty
open Term
open Theory
open Pgm_types
open Pgm_types.T

type namespace = private {
  ns_ex : esymbol   Util.Mstr.t;  (* exception symbols *)
  ns_ns : namespace Util.Mstr.t;  (* inner namespaces *)
}

val ns_find_ex : namespace -> string list -> esymbol
val ns_find_ns : namespace -> string list -> namespace

(** a module under construction *)
type uc

val namespace : uc -> namespace
val impure_uc : uc -> Theory.theory_uc
val effect_uc : uc -> Theory.theory_uc
val pure_uc   : uc -> Theory.theory_uc

(** a module *)
type t = private {
  m_name   : ident;
  m_impure : Theory.theory;
  m_effect : Theory.theory;
  m_pure   : Theory.theory;
  m_decls  : Pgm_ttree.decl list;
  m_export : namespace;
}

val create_module : ?path:string list -> preid -> uc
val close_module : uc -> t

val open_namespace  : uc -> uc
val close_namespace : uc -> bool -> string option -> uc

val use_export : uc -> t -> uc
val use_export_theory : uc -> Theory.theory -> uc

(** insertion *)

exception ClashSymbol of string

(* val add_psymbol : psymbol -> uc -> uc *)
val add_esymbol : esymbol -> uc -> uc
(* val add_mtsymbol : mtsymbol -> uc -> uc *)
val add_decl : Pgm_ttree.decl -> uc -> uc

val add_impure_decl : Decl.decl -> uc -> uc
val add_effect_decl : Decl.decl -> uc -> uc
val add_pure_decl : Decl.decl -> uc -> uc

val add_impure_pdecl :
  Env.env -> Theory.theory Util.Mstr.t -> Ptree.decl -> uc -> uc
val add_effect_pdecl :
  Env.env -> Theory.theory Util.Mstr.t -> Ptree.decl -> uc -> uc
val add_pure_pdecl :
  Env.env -> Theory.theory Util.Mstr.t -> Ptree.decl -> uc -> uc

val add_pdecl :
  Env.env -> Theory.theory Util.Mstr.t -> Ptree.decl -> uc -> uc
  (** add in impure, effect and pure *)

(** builtins *)

val ts_mark : tysymbol
val ty_mark : ty

val ts_unit : tysymbol
val ty_unit : ty

val fs_old : lsymbol
val fs_at  : lsymbol

val vs_old : vsymbol
val vs_now : vsymbol

val th_prelude : theory

(** exceptions *)

exception CloseModule
