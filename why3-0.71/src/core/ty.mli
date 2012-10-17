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
open Ident

(** Types *)

type tvsymbol = private {
  tv_name : ident;
}

module Mtv : Map.S with type key = tvsymbol
module Stv : Mtv.Set
module Htv : Hashtbl.S with type key = tvsymbol

val tv_equal : tvsymbol -> tvsymbol -> bool

val tv_hash : tvsymbol -> int

val create_tvsymbol : preid -> tvsymbol

(* type symbols and types *)

type tysymbol = private {
  ts_name : ident;
  ts_args : tvsymbol list;
  ts_def  : ty option;
}

and ty = private {
  ty_node : ty_node;
  ty_tag  : Hashweak.tag;
}

and ty_node = private
  | Tyvar of tvsymbol
  | Tyapp of tysymbol * ty list

module Mts : Map.S with type key = tysymbol
module Sts : Mts.Set
module Hts : Hashtbl.S with type key = tysymbol
module Wts : Hashweak.S with type key = tysymbol

module Mty : Map.S with type key = ty
module Sty : Mty.Set
module Hty : Hashtbl.S with type key = ty
module Wty : Hashweak.S with type key = ty

val ts_equal : tysymbol -> tysymbol -> bool
val ty_equal : ty -> ty -> bool

val ts_hash : tysymbol -> int
val ty_hash : ty -> int

exception BadTypeArity of tysymbol * int * int
exception DuplicateTypeVar of tvsymbol
exception UnboundTypeVar of tvsymbol

val create_tysymbol : preid -> tvsymbol list -> ty option -> tysymbol

val ty_var : tvsymbol -> ty
val ty_app : tysymbol -> ty list -> ty

(** {3 generic traversal functions} *)
(** traverse only one level of constructor, if you want full traversal
    you need to call those function inside your function *)
val ty_map : (ty -> ty) -> ty -> ty
val ty_fold : ('a -> ty -> 'a) -> 'a -> ty -> 'a
val ty_all : (ty -> bool) -> ty -> bool
val ty_any : (ty -> bool) -> ty -> bool

(** {3 variable-wise map/fold} *)
(** visits every variable of the type *)
val ty_v_map : (tvsymbol -> ty) -> ty -> ty
val ty_v_fold : ('a -> tvsymbol -> 'a) -> 'a -> ty -> 'a
val ty_v_all : (tvsymbol -> bool) -> ty -> bool
val ty_v_any : (tvsymbol -> bool) -> ty -> bool

(** {3 symbol-wise map/fold} *)
(** visits every symbol of the type *)
val ty_s_map : (tysymbol -> tysymbol) -> ty -> ty
val ty_s_fold : ('a -> tysymbol -> 'a) -> 'a -> ty -> 'a
val ty_s_all : (tysymbol -> bool) -> ty -> bool
val ty_s_any : (tysymbol -> bool) -> ty -> bool

exception TypeMismatch of ty * ty

val ty_match : ty Mtv.t -> ty -> ty -> ty Mtv.t
val ty_inst  : ty Mtv.t -> ty -> ty
val ty_freevars : Stv.t -> ty -> Stv.t
val ty_closed : ty -> bool

val ty_equal_check : ty -> ty -> unit

(* built-in symbols *)

val ts_int  : tysymbol
val ts_real : tysymbol

val ty_int  : ty
val ty_real : ty

val ts_func : tysymbol
val ts_pred : tysymbol

val ty_func : ty -> ty -> ty
val ty_pred : ty -> ty

val ts_tuple : int -> tysymbol
val ty_tuple : ty list -> ty

val is_ts_tuple : tysymbol -> bool
val is_ts_tuple_id : ident -> int option

(** {2 Operations on [ty option]} *)

exception UnexpectedProp

val oty_equal : ty option -> ty option -> bool
val oty_hash  : ty option -> int

val oty_type : ty option -> ty
val oty_cons : ty list -> ty option -> ty list

val oty_match : ty Mtv.t -> ty option -> ty option -> ty Mtv.t
val oty_inst  : ty Mtv.t -> ty option -> ty option
val oty_freevars : Stv.t -> ty option -> Stv.t

