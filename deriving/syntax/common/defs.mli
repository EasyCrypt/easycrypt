(* Copyright Jeremy Yallop 2007.
   Copyright Grégoire Henry 2011.
   This file is free software, distributed under the MIT license.
   See the file COPYING for details.
*)

open Camlp4.PreCast

module type Loc = sig
  val _loc : Loc.t (* location of the type definition being derived *)
end

module type Class = sig
  val generate: Type.decl list -> Ast.str_item
  val generate_sigs: Type.decl list -> Ast.sig_item
end

module type ClassBuilder = functor (Loc: Loc) -> Class

module type FullClass = sig
  val classname: Type.name
  val runtimename: Type.name
  include Class
  val generate_expr:
    Ast.module_expr Type.EMap.t ->
    Type.qname Type.NameMap.t ->
    Type.expr -> Ast.module_expr
end

module type FullClassBuilder = functor (L: Loc) -> FullClass

module type ClassDescription = sig
  val classname: Type.name
  val runtimename: Type.name
  val default_module: Type.name option
  val alpha: Type.name option
  val allow_private: bool
  val predefs: (Type.qname * Type.qname) list
  val depends: (module FullClassBuilder) list
end

type generator = (module ClassDescription) * (module ClassBuilder)
