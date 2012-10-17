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
open Util
open Ident
open Ty
open Theory
open Term
open Decl

(* program type symbols *)

type mtsymbol = private {
  mt_impure   : tysymbol;
  mt_effect   : tysymbol;
  mt_pure     : tysymbol;
  mt_regions  : int;
  mt_singleton: bool;
}

val create_mtsymbol :
  impure:tysymbol -> effect:tysymbol -> pure:tysymbol -> singleton:bool ->
  mtsymbol

val mt_equal : mtsymbol -> mtsymbol -> bool

val get_mtsymbol : tysymbol -> mtsymbol

val print_mt_symbol : Format.formatter -> mtsymbol -> unit

val is_mutable_ts : tysymbol -> bool
val is_mutable_ty : ty       -> bool

val is_singleton_ts : tysymbol -> bool
val is_singleton_ty : ty       -> bool

(* builtin logic symbols for programs *)

val ts_arrow : tysymbol
val make_arrow_type : ty list -> ty -> ty

val ts_exn : tysymbol
val ty_exn : ty

(* val ts_label : tysymbol *)

(* regions *)
module R : sig

  type t = private {
    r_tv : tvsymbol;
    r_ty : Ty.ty;    (* effect type *)
  }

  val create : tvsymbol -> Ty.ty -> t

  val print : Format.formatter -> t -> unit

end

module Mreg : Stdlib.Map.S with type key = R.t

module Sreg : Mreg.Set

(* exception sets *)
module Sexn : Set.S with type elt = lsymbol

(* program types *)

module rec T : sig

  type pre = Term.term

  type post_fmla = Term.vsymbol (* result *) * Term.term
  type exn_post_fmla = Term.vsymbol (* result *) option * Term.term

  type esymbol = lsymbol

  type post = post_fmla * (esymbol * exn_post_fmla) list

  type type_v = private
  | Tpure    of ty
  | Tarrow   of pvsymbol list * type_c

  and type_c = {
    c_result_type : type_v;
    c_effect      : E.t;
    c_pre         : pre;
    c_post        : post;
  }

  and pvsymbol = private {
    pv_name   : ident;
    pv_tv     : type_v;
    pv_effect : vsymbol;
    pv_pure   : vsymbol;
    pv_regions: Sreg.t;
  }

  val tpure  : ty -> type_v
  val tarrow : pvsymbol list -> type_c -> type_v

  val create_pvsymbol :
    preid -> type_v ->
    effect:vsymbol -> pure:vsymbol -> regions:Sreg.t -> pvsymbol

  (* program symbols *)

  type psymbol_kind =
    | PSvar   of pvsymbol
    | PSfun   of type_v
    | PSlogic

  type psymbol = {
    ps_effect : lsymbol;
    ps_pure   : lsymbol;
    ps_kind   : psymbol_kind;
  }

  val create_psymbol:
    ?impure:lsymbol -> effect:lsymbol -> pure:lsymbol -> kind:psymbol_kind ->
    psymbol
  val create_psymbol_fun: preid -> type_v -> lsymbol * psymbol
  val create_psymbol_var: pvsymbol -> lsymbol * psymbol

  val get_psymbol: lsymbol -> psymbol

  val ps_name : psymbol -> ident
  val ps_equal : psymbol -> psymbol -> bool

  (* program types -> logic types *)

  val purify : ty -> ty
  val effectify : ty -> ty

  val trans_type_v : ?effect:bool -> ?pure:bool -> type_v -> ty

  (* operations on program types *)

  val apply_type_v_var : type_v -> pvsymbol -> type_c

  val subst_type_v : ty Mtv.t -> term Mvs.t -> type_v -> type_v

  val occur_type_v : R.t -> type_v -> bool

  val v_result : ty -> vsymbol
  val exn_v_result : Why3.Term.lsymbol -> Why3.Term.vsymbol option

  val post_map : (term -> term) -> post -> post

  val eq_type_v : type_v -> type_v -> bool

  (* pretty-printers *)

  val print_type_v : Format.formatter -> type_v -> unit
  val print_type_c : Format.formatter -> type_c -> unit
  val print_pre    : Format.formatter -> pre    -> unit
  val print_post   : Format.formatter -> post   -> unit
  val print_pvsymbol : Format.formatter -> pvsymbol -> unit

end

and Spv :  sig include Set.S with type elt = T.pvsymbol end
and Mpv :  sig include Map.S with type key = T.pvsymbol end

(* effects *)
and E : sig

  type t = private {
    reads  : Sreg.t;
    writes : Sreg.t;
    raises : Sexn.t;
  }

  val empty : t

  val add_read  : R.t -> t -> t
  val add_write : R.t -> t -> t
  val add_raise : T.esymbol -> t -> t
  val add_var   : T.pvsymbol -> t -> t

  val remove : Sreg.t -> t -> t
  val filter : (R.t -> bool) -> t -> t

  val remove_raise : T.esymbol -> t -> t

  val union : t -> t -> t

  val equal : t -> t -> bool

  val no_side_effect : t -> bool

  val subst : Ty.ty Mtv.t -> t -> t

  val occur : R.t -> t -> bool

  val print : Format.formatter -> t -> unit
  val print_rset : Format.formatter -> Sreg.t -> unit

end

(* ghost code *)
(****
val mt_ghost   : mtsymbol
val ps_ghost   : T.psymbol
val ps_unghost : T.psymbol
****)
