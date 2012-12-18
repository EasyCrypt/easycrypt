(* Copyright Jeremy Yallop 2007.
   This file is free software, distributed under the MIT license.
   See the file COPYING for details.
*)

(* Extend the OCaml grammar to include the `deriving' clause after
   type declarations in structure and signatures. *)

open Utils

open Camlp4.PreCast

let instantiate _loc t classname =
  try
    let class_ = Base.find classname in
    let module U = Type.Untranslate(struct let _loc = _loc end) in
    let binding = Ast.TyDcl (_loc, "inline", [], t, []) in
    let decls = Base.display_errors _loc Type.Translate.decls binding in
    if List.exists Base.contains_tvars_decl decls then
      Base.fatal_error _loc ("deriving: type variables cannot be used in `method' instantiations");
    let tdecls = List.map U.decl decls in
    let m = Base.derive_str _loc decls class_ in
    <:module_expr< struct
      type $list:tdecls$
	$m$
      include $uid:classname ^ "_inline"$
    end >>
  with Base.NoSuchClass classname ->
    Base.fatal_error _loc ("deriving: " ^ classname ^ " is not a known `class'")

module Deriving (S : Camlp4.Sig.Camlp4Syntax) = struct

  include Syntax

  open Ast

  EXTEND Gram
  expr: LEVEL "simple"
  [
  [ TRY [e1 = val_longident ; "<" ; t = ctyp; ">" ->
     match e1 with
       | <:ident< $uid:classname$ . $lid:methodname$ >> ->
	   let m = instantiate _loc t classname in
	   <:expr< let module $uid:classname$ = $m$
                   in $uid:classname$.$lid:methodname$ >>
       | _ ->
           Base.fatal_error _loc ("deriving: this looks a bit like a method application, but "
                            ^"the syntax is not valid");
  ]]];

  module_expr: LEVEL "simple"
  [
  [ TRY [e1 = val_longident ; "<" ; t = ctyp; ">" ->
     match e1 with
       | <:ident< $uid:classname$ >> ->
	   instantiate _loc t classname
       | _ ->
           Base.fatal_error _loc ("deriving: this looks a bit like a class instantiation, but "
                            ^"the syntax is not valid");
  ]]];
  END

end

module M = Camlp4.Register.OCamlSyntaxExtension(Id)(Deriving)
