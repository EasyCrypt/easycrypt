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
open Stdlib
open Task

module Mtyl : Map.S with type key = ty list

type tenv =
  | Complete (* The transformation keep the polymorphism *)
  | Incomplete (* The environnement when the transformation isn't complete*)

type env = {
  etenv : tenv;
  ekeep : Sty.t;
  prop_toremove : ty Mtv.t Mpr.t;
  eprojty : ty Mty.t;
  edefined_lsymbol : lsymbol Mtyl.t Mls.t;
  edefined_tsymbol : tysymbol Mtyl.t Mts.t;
}

type auto_clone =  task -> tenv -> Sty.t -> task * env

val create_env : task -> tenv -> Sty.t -> task * env

val t : auto_clone -> Task.task Trans.trans
