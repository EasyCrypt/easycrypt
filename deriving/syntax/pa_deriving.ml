(* Copyright Jeremy Yallop 2007.
   Copyright Grégoire Henry 2011.
   This file is free software, distributed under the MIT license.
   See the file COPYING for details.
*)

(* Extend the OCaml grammar to include the `deriving' clause after
   type declarations in structure and signatures. *)

open Pa_deriving_common.Utils

module Deriving (Syntax : Camlp4.Sig.Camlp4Syntax) =
struct

  open Pa_deriving_common.Base
  open Pa_deriving_common.Type
  open Pa_deriving_common.Extend
  open Camlp4.PreCast
  include Syntax

  DELETE_RULE Gram str_item: "type"; type_declaration END
  DELETE_RULE Gram sig_item: "type"; type_declaration END

  open Ast


  EXTEND Gram
  str_item:
  [[ "type"; types = type_declaration -> <:str_item< type $types$ >>
    | "type"; types = type_declaration; "deriving"; "("; cl = LIST0 [x = UIDENT -> x] SEP ","; ")" ->
       try
	 let decls = display_errors _loc Translate.decls types in
         let module U = Untranslate(struct let _loc = _loc end) in
	 let cl = List.map find cl in
         let tdecls = List.map U.decl decls in
         <:str_item< type $list:tdecls$ $list:List.map (derive_str _loc decls) cl$ >>
       with NoSuchClass classname ->
	 fatal_error _loc ("deriving: " ^ classname ^ " is not a known `class'")
   ]]
  ;
  sig_item:
  [[ "type"; types = type_declaration -> <:sig_item< type $types$ >>
   | "type"; types = type_declaration; "deriving"; "("; cl = LIST0 [x = UIDENT -> x] SEP "," ; ")" ->
       try
	 let decls  = display_errors _loc Translate.decls types in
	 let module U = Untranslate(struct let _loc = _loc end) in
	 let tdecls = List.concat_map U.sigdecl decls in
	 let cl = List.map find cl in
	 let ms = List.map (derive_sig _loc decls) cl in
         <:sig_item< type $list:tdecls$ $list:ms$ >>
       with NoSuchClass classname ->
	 fatal_error _loc ("deriving: " ^ classname ^ " is not a known `class'")
]]
  ;
  END

end

module M = Camlp4.Register.OCamlSyntaxExtension(Pa_deriving_common.Id)(Deriving)
