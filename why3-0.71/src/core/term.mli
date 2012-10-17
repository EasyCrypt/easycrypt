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
open Ty

(** Terms and Formulas *)

(** {2 Variable symbols} *)

type vsymbol = private {
  vs_name : ident;
  vs_ty   : ty;
}

module Mvs : Map.S with type key = vsymbol
module Svs : Mvs.Set
module Hvs : Hashtbl.S with type key = vsymbol

val vs_equal : vsymbol -> vsymbol -> bool
val vs_hash : vsymbol -> int

val create_vsymbol : preid -> ty -> vsymbol

(** {2 Function and predicate symbols} *)

type lsymbol = private {
  ls_name   : ident;
  ls_args   : ty list;
  ls_value  : ty option;
}

module Mls : Map.S with type key = lsymbol
module Sls : Mls.Set
module Hls : Hashtbl.S with type key = lsymbol
module Wls : Hashweak.S with type key = lsymbol

val ls_equal : lsymbol -> lsymbol -> bool
val ls_hash : lsymbol -> int

val create_lsymbol : preid -> ty list -> ty option -> lsymbol
val create_fsymbol : preid -> ty list -> ty -> lsymbol
val create_psymbol : preid -> ty list -> lsymbol

val ls_ty_freevars : lsymbol -> Stv.t

(** {2 Exceptions} *)

exception EmptyCase
exception DuplicateVar of vsymbol
exception UncoveredVar of vsymbol
exception BadArity of lsymbol * int * int
exception FunctionSymbolExpected of lsymbol
exception PredicateSymbolExpected of lsymbol

(** {2 Patterns} *)

type pattern = private {
  pat_node : pattern_node;
  pat_vars : Svs.t;
  pat_ty   : ty;
  pat_tag  : int;
}

and pattern_node = private
  | Pwild
  | Pvar of vsymbol
  | Papp of lsymbol * pattern list
  | Por  of pattern * pattern
  | Pas  of pattern * vsymbol

val pat_equal : pattern -> pattern -> bool
val pat_hash : pattern -> int

(** Smart constructors for patterns *)

val pat_wild : ty -> pattern
val pat_var : vsymbol -> pattern
val pat_app : lsymbol -> pattern list -> ty -> pattern
val pat_or  : pattern -> pattern -> pattern
val pat_as  : pattern -> vsymbol -> pattern

(** Generic traversal functions *)

val pat_map : (pattern -> pattern) -> pattern -> pattern
val pat_fold : ('a -> pattern -> 'a) -> 'a -> pattern -> 'a
val pat_all : (pattern -> bool) -> pattern -> bool
val pat_any : (pattern -> bool) -> pattern -> bool

(** {2 Terms and Formulas} *)

type quant =
  | Tforall
  | Texists

type binop =
  | Tand
  | Tor
  | Timplies
  | Tiff

type integer_constant =
  | IConstDecimal of string
  | IConstHexa of string
  | IConstOctal of string
  | IConstBinary of string

type real_constant =
  | RConstDecimal of string * string * string option (* int / frac / exp *)
  | RConstHexa of string * string * string

type constant =
  | ConstInt of integer_constant
  | ConstReal of real_constant

type term = private {
  t_node  : term_node;
  t_ty    : ty option;
  t_label : label list;
  t_loc   : Loc.position option;
  t_vars  : int Mvs.t;
  t_tag   : int;
}

and term_node = private
  | Tvar of vsymbol
  | Tconst of constant
  | Tapp of lsymbol * term list
  | Tif of term * term * term
  | Tlet of term * term_bound
  | Tcase of term * term_branch list
  | Teps of term_bound
  | Tquant of quant * term_quant
  | Tbinop of binop * term * term
  | Tnot of term
  | Ttrue
  | Tfalse

and term_bound
and term_branch
and term_quant

and trigger = term list list

module Mterm : Map.S with type key = term
module Sterm : Mterm.Set
module Hterm : Hashtbl.S with type key = term

val t_equal : term -> term -> bool
val t_hash : term -> int

(** Bindings *)

(** close bindings *)

val t_close_bound : vsymbol -> term -> term_bound
val t_close_branch : pattern -> term -> term_branch
val t_close_quant : vsymbol list -> trigger -> term -> term_quant

(** open bindings *)

val t_open_bound : term_bound -> vsymbol * term
val t_open_branch : term_branch -> pattern * term
val t_open_quant : term_quant -> vsymbol list * trigger * term

(** open bindings with optimized closing callbacks *)

val t_open_bound_cb :
  term_bound -> vsymbol * term * (vsymbol -> term -> term_bound)

val t_open_branch_cb :
  term_branch -> pattern * term * (pattern -> term -> term_branch)

val t_open_quant_cb :
  term_quant -> vsymbol list * trigger * term *
              (vsymbol list -> trigger -> term -> term_quant)

(** Type checking *)

exception TermExpected of term
exception FmlaExpected of term

val t_type : term -> ty
(** [t_type t] checks that [t] is value-typed and returns its type *)

val t_prop : term -> term
(** [t_prop t] checks that [t] is prop-typed and returns [t] *)

val t_ty_check : term -> ty option -> unit
(** [t_ty_check t ty] checks that the type of [t] is [ty] *)

(** Smart constructors for terms and formulas *)

val t_app  : lsymbol -> term list -> ty option -> term
val fs_app : lsymbol -> term list -> ty -> term
val ps_app : lsymbol -> term list -> term

val t_app_infer : lsymbol -> term list -> term
val ls_arg_inst : lsymbol -> term list -> ty Mtv.t
val ls_app_inst : lsymbol -> term list -> ty option -> ty Mtv.t

val t_var : vsymbol -> term
val t_const : constant -> term
val t_int_const : string -> term
val t_real_const : real_constant -> term
val t_if : term -> term -> term -> term
val t_let : term -> term_bound -> term
val t_case : term -> term_branch list -> term
val t_eps : term_bound -> term
val t_quant : quant -> term_quant -> term
val t_forall : term_quant -> term
val t_exists : term_quant -> term
val t_binary : binop -> term -> term -> term
val t_and : term -> term -> term
val t_or : term -> term -> term
val t_implies : term -> term -> term
val t_iff : term -> term -> term
val t_not : term -> term
val t_true : term
val t_false : term

val asym_label : label
val t_and_asym : term -> term -> term
val t_or_asym : term -> term -> term

val t_let_close : vsymbol -> term -> term -> term
val t_eps_close : vsymbol -> term -> term
val t_quant_close : quant -> vsymbol list -> trigger -> term -> term
val t_forall_close : vsymbol list -> trigger -> term -> term
val t_exists_close : vsymbol list -> trigger -> term -> term

val t_label : ?loc:Loc.position -> label list -> term -> term
val t_label_add : label -> term -> term
val t_label_copy : term -> term -> term

(** Constructors with propositional simplification *)

val t_if_simp : term -> term -> term -> term
val t_let_simp : term -> term_bound -> term
val t_quant_simp : quant -> term_quant -> term
val t_forall_simp : term_quant -> term
val t_exists_simp : term_quant -> term
val t_binary_simp : binop -> term -> term -> term
val t_and_simp : term -> term -> term
val t_and_simp_l : term list -> term
val t_or_simp : term -> term -> term
val t_or_simp_l : term list -> term
val t_implies_simp : term -> term -> term
val t_iff_simp : term -> term -> term
val t_not_simp : term -> term

val t_and_asym_simp : term -> term -> term
val t_and_asym_simp_l : term list -> term
val t_or_asym_simp : term -> term -> term
val t_or_asym_simp_l : term list -> term

val t_let_close_simp : vsymbol -> term -> term -> term
val t_quant_close_simp : quant -> vsymbol list -> trigger -> term -> term
val t_forall_close_simp : vsymbol list -> trigger -> term -> term
val t_exists_close_simp : vsymbol list -> trigger -> term -> term

val t_forall_close_merge : vsymbol list -> term -> term
(** [forall_close_merge vs f] puts a universal quantifier over [f];
    merges variable lists if [f] is already universally quantified;
    reuses triggers of [f], if any, otherwise puts no triggers. *)

(** Built-in symbols *)

val ps_equ : lsymbol  (* equality predicate *)

val t_equ : term -> term -> term
val t_neq : term -> term -> term

val t_equ_simp : term -> term -> term
val t_neq_simp : term -> term -> term

val fs_tuple : int -> lsymbol   (* n-tuple *)
val t_tuple : term list -> term

val is_fs_tuple : lsymbol -> bool
val is_fs_tuple_id : ident -> int option

val fs_func_app : lsymbol  (* value-typed higher-order application *)
val ps_pred_app : lsymbol  (* prop-typed higher-order application *)

val t_func_app : term -> term -> term
val t_pred_app : term -> term -> term

val t_func_app_l : term -> term list -> term
val t_pred_app_l : term -> term list -> term

(** {2 Term library} *)

(** One-level (non-recursive) term traversal *)

val t_map : (term -> term) -> term -> term
val t_fold : ('a -> term -> 'a) -> 'a -> term -> 'a
val t_map_fold : ('a -> term -> 'a * term) -> 'a -> term -> 'a * term

val t_all : (term -> bool) -> term -> bool
val t_any : (term -> bool) -> term -> bool

(** Special maps *)

val t_map_simp : (term -> term) -> term -> term
(** [t_map_simp] reconstructs the term using simplification constructors *)

val t_map_sign : (bool -> term -> term) -> bool -> term -> term
(** [t_map_sign] passes a polarity parameter, unfolds if-then-else and iff *)

val t_map_cont : ((term -> 'a) -> term -> 'a) -> (term -> 'a) -> term -> 'a
(** [t_map_cont] is [t_map] in continuation-passing style *)

val list_map_cont: (('a -> 'b) -> 'c -> 'b) -> ('a list -> 'b) -> 'c list -> 'b

(** Trigger traversal *)

val tr_equal : trigger -> trigger -> bool
val tr_map : (term -> term) -> trigger -> trigger
val tr_fold : ('a -> term -> 'a) -> 'a -> trigger -> 'a
val tr_map_fold : ('a -> term -> 'a * term) -> 'a -> trigger -> 'a * trigger

(** Traversal with separate functions for value-typed and prop-typed terms *)

module TermTF : sig

  val t_select : (term -> 'a) -> (term -> 'a) -> term -> 'a
  (** [t_select fnT fnF t] is [fnT t] if [t] is a value, [fnF t] otherwise *)

  val t_selecti : ('a -> term -> 'b) -> ('a -> term -> 'b) -> 'a -> term -> 'b
  (** [t_selecti fnT fnF acc t] is [t_select (fnT acc) (fnF acc) t] *)

  val t_map : (term -> term) -> (term -> term) -> term -> term
  (** [t_map fnT fnF = t_map (t_select fnT fnF)] *)

  val t_fold : ('a -> term -> 'a) -> ('a -> term -> 'a) -> 'a -> term -> 'a
  (** [t_fold fnT fnF = t_fold (t_selecti fnT fnF)] *)

  val t_map_fold : ('a -> term -> 'a * term) ->
    ('a -> term -> 'a * term) -> 'a -> term -> 'a * term

  val t_all : (term -> bool) -> (term -> bool) -> term -> bool
  val t_any : (term -> bool) -> (term -> bool) -> term -> bool

  val t_map_simp : (term -> term) -> (term -> term) -> term -> term

  val t_map_sign : (bool -> term -> term) ->
    (bool -> term -> term) -> bool -> term -> term

  val t_map_cont : ((term -> 'a) -> term -> 'a) ->
    ((term -> 'a) -> term -> 'a) -> (term -> 'a) -> term -> 'a

  val tr_map : (term -> term) -> (term -> term) -> trigger -> trigger

  val tr_fold : ('a -> term -> 'a) -> ('a -> term -> 'a) -> 'a -> trigger -> 'a

  val tr_map_fold : ('a -> term -> 'a * term) ->
    ('a -> term -> 'a * term) -> 'a -> trigger -> 'a * trigger
end

(** Map/fold over free variables *)

val t_v_map : (vsymbol -> term) -> term -> term
val t_v_fold : ('a -> vsymbol -> 'a) -> 'a -> term -> 'a
val t_v_all : (vsymbol -> bool) -> term -> bool
val t_v_any : (vsymbol -> bool) -> term -> bool

(** Variable substitution *)

val t_subst : term Mvs.t -> term -> term
val t_subst_single : vsymbol -> term -> term -> term

val t_ty_subst : ty Mtv.t -> term Mvs.t -> term -> term

(** Find free variables and type variables *)

val t_freevars    : int Mvs.t -> term -> int Mvs.t
val t_ty_freevars : Stv.t -> term -> Stv.t

(** Map/fold over types and logical symbols in terms and patterns *)

val t_s_map : (ty -> ty) -> (lsymbol -> lsymbol) -> term -> term
val t_s_fold : ('a -> ty -> 'a) -> ('a -> lsymbol -> 'a) -> 'a -> term -> 'a

val t_s_all : (ty -> bool) -> (lsymbol -> bool) -> term -> bool
val t_s_any : (ty -> bool) -> (lsymbol -> bool) -> term -> bool

val t_ty_map : (ty -> ty) -> term -> term
val t_ty_fold : ('a -> ty -> 'a) -> 'a -> term -> 'a

(* Map/fold over applications in terms (but not in patterns!) *)

val t_app_map :
  (lsymbol -> ty list -> ty option -> lsymbol) -> term -> term

val t_app_fold :
  ('a -> lsymbol -> ty list -> ty option -> 'a) -> 'a -> term -> 'a

(** Equality modulo alpha *)

val t_equal_alpha : term -> term -> bool

module Hterm_alpha : Hashtbl.S with type key = term

(** Subterm occurrence check and replacement *)

val t_occurs : term -> term -> bool
val t_occurs_alpha : term -> term -> bool

val t_replace : term -> term -> term -> term
val t_replace_alpha : term -> term -> term -> term

