(* Copyright Jeremy Yallop 2007.
   This file is free software, distributed under the MIT license.
   See the file COPYING for details.
*)

open Pa_deriving_common
open Utils

module Description : Defs.ClassDescription = struct
  let classname = "Enum"
  let runtimename = "Deriving_Enum"
  let default_module = Some "Defaults"
  let alpha = None
  let allow_private = false
  let predefs = [
    ["int"], ["Deriving_Enum";"int"];
    ["bool"], ["Deriving_Enum";"bool"];
    ["unit"], ["Deriving_Enum";"unit"];
    ["char"], ["Deriving_Enum";"char"];
  ]
  let depends = []
end

module Builder(Loc : Defs.Loc) = struct


  module Helpers = Base.AstHelpers(Loc)
  module Generator = Base.Generator(Loc)(Description)

  open Loc
  open Camlp4.PreCast
  open Description

  let wrap numbering = [ <:str_item< let numbering = $numbering$ >> ]

  let generator = (object(self)

    inherit Generator.generator

    method proxy unit =
      None, [ <:ident< succ >>;
	      <:ident< pred >>;
	      <:ident< to_enum >>;
	      <:ident< from_enum >>;
	      <:ident< enum_from >>;
	      <:ident< enum_from_then >>;
	      <:ident< enum_from_to >>;
	      <:ident< enum_from_then_to >>; ]

    method sum ?eq ctxt tname params constraints summands =
    let numbering =
      List.fold_right2
        (fun n ctor rest ->
           match ctor with
             | (name, []) -> <:expr< ($uid:name$, $`int:n$) :: $rest$ >>
             | (name,_) ->
		 raise (Base.Underivable
			  (classname ^ " cannot be derived for the type "
			   ^ tname ^" because the constructor "
                           ^ name^" is not nullary")))
        (List.range 0 (List.length summands))
        summands
        <:expr< [] >> in
    wrap numbering

    method variant ctxt tname params constraints (_, tags) =
    let numbering =
      List.fold_right2
        (fun n tagspec rest ->
           match tagspec with
             | Type.Tag (name, []) -> <:expr< (`$name$, $`int:n$) :: $rest$ >>
             | Type.Tag (name, _) ->
		 raise (Base.Underivable
			  (classname ^" cannot be derived because the tag "
                           ^ name^" is not nullary"))
             | _ -> raise (Base.Underivable
			     (classname ^" cannot be derived for this "
                              ^"polymorphic variant type")))
        (List.range 0 (List.length tags))
        tags
        <:expr< [] >> in
    wrap numbering

    method tuple ctxt tys =
      match tys with
      | [ty] -> wrap <:expr< $self#call_expr ctxt ty "numbering"$ >>
      | _ ->
	  raise (Base.Underivable (classname ^" cannot be derived for tuple types"))

    method record ?eq _ tname params constraints =
      raise (Base.Underivable
	       (classname ^" cannot be derived for record types (i.e. "^tname^")"))

  end :> Generator.generator)

  let generate = Generator.generate generator
  let generate_sigs = Generator.generate_sigs generator

end

module Enum = Base.Register(Description)(Builder)
