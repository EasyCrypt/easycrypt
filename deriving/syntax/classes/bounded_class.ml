(* Copyright Jeremy Yallop 2007.
   This file is free software, distributed under the MIT license.
   See the file COPYING for details.
*)

open Pa_deriving_common
open Utils

module Description : Defs.ClassDescription = struct
  let classname = "Bounded"
  let runtimename = "Deriving_Bounded"
  let default_module = None
  let alpha = None
  let allow_private = false
  let predefs = [
    ["unit"], ["Deriving_Bounded";"unit"];
    ["bool"], ["Deriving_Bounded";"bool"];
    ["char"], ["Deriving_Bounded";"char"];
    ["int"], ["Deriving_Bounded";"int"];
    ["int32"], ["Deriving_Bounded";"int32"];
    ["Int32";"t"], ["Deriving_Bounded";"int32"];
    ["int64"], ["Deriving_Bounded";"int64"];
    ["Int64";"t"], ["Deriving_Bounded";"int64"];
    ["nativeint"], ["Deriving_Bounded";"nativeint"];
    ["open_flag"], ["Deriving_Bounded";"open_flag"];
    ["fpclass"], ["Deriving_Bounded";"fpclass"];
  ]
  let depends = []
end

module Builder(Loc : Defs.Loc) = struct

  module Helpers = Base.AstHelpers(Loc)
  module Generator = Base.Generator(Loc)(Description)

  open Loc
  open Camlp4.PreCast
  open Description

  let wrap min max =
    [ <:str_item< let min_bound = $min$ >>; <:str_item< let max_bound = $max$ >> ]

  let generator = (object (self)

    inherit Generator.generator

    method proxy unit =
      None, [ <:ident< min_bound >>;
	      <:ident< max_bound >>; ]

    method tuple ctxt ts =
      let expr t =
	let e = self#expr ctxt t in
        <:expr< let module M = $e$ in M.min_bound >>,
        <:expr< let module M = $e$ in M.max_bound >> in
      let minBounds, maxBounds = List.split (List.map expr ts) in
      wrap (Helpers.tuple_expr minBounds) (Helpers.tuple_expr maxBounds)

    method sum ?eq ctxt tname params constraints summands =
      let extract_name = function
        | (name,[]) -> name
        | (name,_) ->
	    raise (Base.Underivable
		     (classname ^" cannot be derived for the type "
                      ^ tname ^ " because the constructor "
                      ^ name ^ " is not nullary")) in
      let names = List.map extract_name summands in
      wrap <:expr< $uid:List.hd names$ >> <:expr< $uid:List.last names$ >>

    method variant ctxt tname params constraints (_, tags) =
      let extract_name = function
        | Type.Tag (name, []) -> name
        | Type.Tag (name, _) ->
	    raise (Base.Underivable
		     (classname^" cannot be derived because "
		      ^ "the tag " ^ name^" is not nullary"))
        | _ ->
	    raise (Base.Underivable
		     (classname^" cannot be derived for this "
                      ^ "polymorphic variant type")) in
      let names = List.map extract_name tags in
      wrap <:expr< `$List.hd names$ >> <:expr< `$List.last names$ >>

    (* should perhaps implement this one *)
    method record ?eq _ tname params constraints =
      raise (Base.Underivable
	       (classname^" cannot be derived for record types (i.e. "
                ^ tname ^ ")"))

  end :> Generator.generator)

  let generate = Generator.generate generator
  let generate_sigs = Generator.generate_sigs generator

end

module Bounded = Base.Register(Description)(Builder)
