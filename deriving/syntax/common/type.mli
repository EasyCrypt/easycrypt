(* Copyright Jeremy Yallop 2007.
   Copyright Grégoire Henry 2011.
   This file is free software, distributed under the MIT license.
   See the file COPYING for details.
*)

open Utils

(* More convenient representation for types, and translation from the
   Camlp4 representation *)

type name = string
type qname = name list

module NameMap : Map.S with type key = string
module NameSet : Set.S with type elt = string

(* *)

type param = name * [ `Minus | `Plus ] option

type decl = name * param list * rhs * constraint_ list * bool

and rhs =
    [ `Expr of expr
    | `Fresh of expr option * repr * [ `Private | `Public ]
    | `Nothing
    | `Variant of variant ]

and repr = Sum of summand list | Record of field list

and field = name * poly_expr * [ `Immutable | `Mutable ]

and summand = name * expr list

and constraint_ = expr * expr

and expr =
    [ `Class of [ `NYI ]
    | `Constr of qname * expr list
    | `Function of expr * expr
    | `Label of [ `NonOptional | `Optional ] * name * expr * expr
    | `Object of [ `NYI ]
    | `Param of param
    | `Tuple of expr list ]

and poly_expr = param list * expr

and variant = [ `Eq | `Gt | `Lt ] * tagspec list

and tagspec = Tag of name * expr list | Extends of expr

module ParamSet : Set.S with type elt = param
module ParamMap : Map.S with type key = param
module ExprSet : Set.S with type elt = expr
module ExprMap : Map.S with type key = expr
module ESet : Set.S with type elt = name * expr list
module EMap : Map.S with type key = name * expr list

val free_tvars : expr -> ParamSet.t
val contains_tvars : expr -> bool
val contains_tvars_decl : decl -> bool

type subst = expr NameMap.t
val build_subst : (name * expr) list -> subst
val substitute_decl : subst -> decl -> decl
val substitute_expr : subst -> expr -> expr
val substitute_rhs : subst -> rhs -> rhs
val substitute_constraint : subst -> constraint_ -> constraint_

(** *)

class virtual ['a] fold : object
  method constraint_ : constraint_ -> 'a
  method virtual crush : 'a list -> 'a
  method decl : decl -> 'a
  method expr : expr -> 'a
  method field : field -> 'a
  method poly_expr : poly_expr -> 'a
  method repr : repr -> 'a
  method rhs : rhs -> 'a
  method summand : summand -> 'a
  method tagspec : tagspec -> 'a
  method variant : variant -> 'a
end

class transform : object
  method constraint_ : constraint_ -> constraint_
  method decl : decl -> decl
  method expr : expr -> expr
  method field : field -> field
  method poly_expr : poly_expr -> poly_expr
  method repr : repr -> repr
  method rhs : rhs -> rhs
  method summand : summand -> summand
  method tagspec : tagspec -> tagspec
  method variant : variant -> variant
end

open Camlp4.PreCast

module Translate : sig

  val param : Ast.ctyp -> string * [> `Minus | `Plus ] option
  val params : Ast.ctyp list -> (string * [> `Minus | `Plus ] option) list
  val split_and : Ast.ctyp -> (Ast.ctyp * Ast.ctyp, Ast.ctyp) either
  val split_comma : Ast.ctyp -> (Ast.ctyp * Ast.ctyp, Ast.ctyp) either
  val split_semi : Ast.ctyp -> (Ast.ctyp * Ast.ctyp, Ast.ctyp) either
  val split_or : Ast.ctyp -> (Ast.ctyp * Ast.ctyp, Ast.ctyp) either
  val split_amp : Ast.ctyp -> (Ast.ctyp * Ast.ctyp,  Ast.ctyp) either
  val split_ofamp : Ast.ctyp -> (Ast.ctyp * Ast.ctyp, Ast.ctyp) either
  val split_star : Ast.ctyp -> (Ast.ctyp * Ast.ctyp, Ast.ctyp) either
  val list :
    (Ast.ctyp -> 'a) ->
    (Ast.ctyp -> (Ast.ctyp * Ast.ctyp, Ast.ctyp) either) ->
    Ast.ctyp -> 'a list
  val ident : Ast.ident -> name
  val qident : Ast.ident -> qname

  type vmap = (name * variant * name option) list

  val fresh_name : unit -> string
  val set_name_prefix : name -> unit

  module WithParams(P : sig val params : param list end) : sig
    val params : param list
    val apply_t : 'a -> [> `Constr of 'a list * [> `Param of param ] list ]
    val expr : Ast.ctyp -> expr * vmap
    val tagspec : Ast.ctyp -> tagspec * vmap
    val application : Ast.ctyp -> (qname * expr list) * vmap
    val variant : Ast.ctyp -> ?alias:name -> [ `Eq | `Gt | `Lt ] -> expr * vmap
    val polyexpr : Ast.ctyp -> poly_expr * vmap
    val field : Ast.ctyp -> field * vmap
    val summand : Ast.ctyp -> summand * vmap
    val repr : Ast.ctyp -> repr * (name * variant * name option) list
    val toplevel : Ast.ctyp -> rhs * vmap
    val constraints : (Ast.ctyp * Ast.ctyp) list -> constraint_ list * vmap
    val declify :
      (name * variant * name option) list ->
      (decl * (name * expr) option) list
  end

  type alias_map = expr NameMap.t

  val build_alias_map : (NameMap.key * expr) option list -> alias_map
  val split : Ast.ctyp -> Ast.ctyp list
  val decl : Ast.ctyp -> decl list * alias_map
  val substitute_aliases : alias_map -> decl -> decl
  val decls : Ast.ctyp -> decl list

end

module type Untranslate = sig

  val param : string * [< `Minus | `Plus ] option -> Ast.ctyp
  val qname : string list -> Ast.ident
  val qName : string list -> Ast.ident
  val expr : expr -> Ast.ctyp
  val poly : param list * expr -> Ast.ctyp
  val rhs : rhs -> Ast.ctyp
  val tagspec : tagspec -> Ast.ctyp
  val summand : summand -> Ast.ctyp
  val field : field -> Ast.ctyp
  val repr : repr -> Ast.ctyp
  val constraint_ : expr * expr -> Ast.ctyp * Ast.ctyp
  val decl : decl -> Ast.ctyp
  val sigdecl : decl -> Ast.ctyp list

end

module Untranslate(C : sig val _loc : Ast.Loc.t end) : Untranslate

(* Debug *)
val print_expr : expr -> string
val print_rhs : rhs -> string
