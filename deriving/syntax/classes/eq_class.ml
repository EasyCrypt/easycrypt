(* Copyright Jeremy Yallop 2007.
   This file is free software, distributed under the MIT license.
   See the file COPYING for details.
*)

open Pa_deriving_common
open Utils

module Description : Defs.ClassDescription = struct
  let classname = "Eq"
  let runtimename = "Deriving_Eq"
  let default_module = None
  let alpha = Some "Eq_alpha"
  let allow_private = true
  let predefs = [
    ["unit"], ["Deriving_Eq";"unit"];
    ["bool"], ["Deriving_Eq";"bool"];
    ["char"], ["Deriving_Eq";"char"];
    ["int"], ["Deriving_Eq";"int"];
    ["int32"], ["Deriving_Eq";"int32"];
    ["Int32";"t"], ["Deriving_Eq";"int32"];
    ["int64"], ["Deriving_Eq";"int64"];
    ["Int64";"t"], ["Deriving_Eq";"int64"];
    ["nativeint"], ["Deriving_Eq";"nativeint"];
    ["float"], ["Deriving_Eq";"float"];
    ["num"], ["Deriving_num";"num"];
    ["list"], ["Deriving_Eq";"list"];
    ["option"], ["Deriving_Eq";"option"];
    ["string"], ["Deriving_Eq";"string"];
    ["ref"], ["Deriving_Eq";"ref"];
    ["array"], ["Deriving_Eq";"array"];
  ]
  let depends = []
end

module Builder(Loc : Defs.Loc) = struct

  module Helpers = Base.AstHelpers(Loc)
  module Generator = Base.Generator(Loc)(Description)

  open Loc
  open Camlp4.PreCast
  open Description

  let lprefix = "l" and rprefix = "r"

  let wrap eq =
    [ <:str_item< let eq l r = match l, r with $list:eq$ >>]

  let generator = (object (self)

    method proxy unit =
      None, [ <:ident< eq >>; ]

    inherit Generator.generator

    method tuple ctxt tys =
      let n = List.length tys in
      let lnames, lpatt, _ = Helpers.tuple ~param:lprefix n in
      let rnames, rpatt, _ = Helpers.tuple ~param:rprefix n in
      let test_and ty (lid, rid) e =
	<:expr< $self#call_expr ctxt ty "eq"$ $lid:lid$ $lid:rid$ && $e$ >> in
      let expr =
        List.fold_right2 test_and tys (List.zip lnames rnames) <:expr< true >> in
      wrap [ <:match_case< (($lpatt$),($rpatt$)) -> $expr$ >> ]


    method case ctxt (name,args) =
      match args with
      | [] -> <:match_case< ($uid:name$, $uid:name$) -> true >>
      | _ ->
          let nargs = List.length args in
          let _, lpatt, lexpr = Helpers.tuple ~param:lprefix nargs
          and _, rpatt, rexpr = Helpers.tuple ~param:rprefix nargs in
	  let patt = <:patt< ($uid:name$ $lpatt$, $uid:name$ $rpatt$) >> in
	  let eq =
	    <:expr< $self#call_expr ctxt (`Tuple args) "eq"$ $lexpr$ $rexpr$ >> in
          <:match_case< $patt$ -> $eq$ >>

    method sum ?eq ctxt tname params constraints summands =
      let wildcard =
	match summands with
	| [_] -> []
	| _ -> [ <:match_case< _ -> false >>] in
      wrap (List.map (self#case ctxt) summands @ wildcard)


    method field ctxt (name, ty, mut) =
      assert(mut <> `Mutable);
      <:expr< $self#call_poly_expr ctxt ty "eq"$ $lid:lprefix ^ name$ $lid:rprefix ^ name$ >>

    method record ?eq ctxt tname params constraints fields =
      if List.exists (function (_,_,`Mutable) -> true | _ -> false) fields then
	wrap [ <:match_case< (l,r) -> l==r >> ]
      else
	let lpatt = Helpers.record_pattern ~prefix:lprefix fields in
	let rpatt = Helpers.record_pattern ~prefix:rprefix fields in
	let test_and f e = <:expr< $self#field ctxt f$ && $e$ >> in
	let expr = List.fold_right test_and fields <:expr< true >> in
	wrap [ <:match_case< (($lpatt$), ($rpatt$)) -> $expr$ >> ]


    method polycase ctxt : Pa_deriving_common.Type.tagspec -> Ast.match_case = function
      | Type.Tag (name, []) -> <:match_case< `$name$, `$name$ -> true >>
      | Type.Tag (name, es) ->
	  <:match_case< `$name$ l, `$name$ r -> $self#call_expr ctxt (`Tuple es) "eq"$ l r >>
      | Type.Extends t ->
          let lpatt, lguard, lcast = Generator.cast_pattern ctxt ~param:"l" t in
          let rpatt, rguard, rcast = Generator.cast_pattern ctxt ~param:"r" t in
	  let patt = <:patt< ($lpatt$, $rpatt$) >> in
	  let eq = <:expr< $self#call_expr ctxt t "eq"$ $lcast$ $rcast$ >> in
          <:match_case< $patt$ when $lguard$ && $rguard$ -> $eq$ >>

    method variant ctxt tname params constraints (spec, tags) =
      wrap (List.map (self#polycase ctxt) tags @ [ <:match_case< _ -> false >> ])

  end :> Generator.generator)

  let classname = Description.classname
  let runtimename = Description.runtimename
  let generate = Generator.generate generator
  let generate_sigs = Generator.generate_sigs generator
  let generate_expr = Generator.generate_expr generator

end

module Eq = Base.Register(Description)(Builder)

let depends = (module Builder : Defs.FullClassBuilder)
