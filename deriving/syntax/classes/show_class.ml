(* Copyright Jeremy Yallop 2007.
   This file is free software, distributed under the MIT license.
   See the file COPYING for details.
*)

open Pa_deriving_common
open Utils

module Description : Defs.ClassDescription = struct
  let classname = "Show"
  let default_module = Some "Defaults"
  let runtimename = "Deriving_Show"
  let alpha = Some "Show_unprintable"
  let allow_private = true
  let predefs = [
    ["int"      ], ["Deriving_Show";"int"];
    ["bool"     ], ["Deriving_Show";"bool"];
    ["unit"     ], ["Deriving_Show";"unit"];
    ["char"     ], ["Deriving_Show";"char"];
    ["int32"    ], ["Deriving_Show";"int32"];
    ["Int32";"t"], ["Deriving_Show";"int32"];
    ["int64"    ], ["Deriving_Show";"int64"];
    ["Int64";"t"], ["Deriving_Show";"int64"];
    ["nativeint"], ["Deriving_Show";"nativeint"];
    ["float"    ], ["Deriving_Show";"float"];
    ["num"      ], ["Deriving_num" ;"num"];
    ["string"   ], ["Deriving_Show";"string"];
    ["list"     ], ["Deriving_Show";"list"];
    ["ref"      ], ["Deriving_Show";"ref"];
    ["option"   ], ["Deriving_Show";"option"];
    ["array"    ], ["Deriving_Show";"array"];
  ]
  let depends = []
end

module Builder(Loc : Defs.Loc) = struct

  module Helpers = Base.AstHelpers(Loc)
  module Generator = Base.Generator(Loc)(Description)

  open Loc
  open Camlp4.PreCast
  open Description

  let wrap formatter =
    [ <:str_item< let format formatter = function $list:formatter$ >> ]

  let in_a_box box i e =
    <:expr<
      Format.$lid:box$ formatter $`int:i$;
      $e$;
      Format.pp_close_box formatter () >>

  let in_paren e =
    <:expr<
      Format.pp_print_string formatter "(";
      $e$;
      Format.pp_print_string formatter ")" >>

  let in_hovbox ?(indent = 0) = in_a_box "pp_open_hovbox" indent
  and in_box ?(indent = 0) = in_a_box "pp_open_box" indent

  let generator = (object (self)

    inherit Generator.generator

    method proxy unit =
      None, [ <:ident< format >>;
	      <:ident< format_list >>;
	      <:ident< show >>;
	      <:ident< show_list >>; ]

    method nargs ctxt tvars args =
      match tvars, args with
      | [id], [ty] ->
	  <:expr< $self#call_expr ctxt ty "format"$ formatter $lid:id$ >>
      | id::ids, ty::tys ->
	  let format_expr id ty =
            <:expr< $self#call_expr ctxt ty "format"$ formatter $lid:id$ >> in
	  let format_expr' id ty =
	    <:expr< Format.pp_print_string formatter ",";
	            Format.pp_print_space formatter ();
	            $format_expr id ty$>> in
	  let exprs = format_expr id ty :: List.map2 format_expr' ids tys in
          in_paren (in_hovbox ~indent:1 (Helpers.seq_list exprs))
      | _ -> assert false

    method tuple ctxt args =
      let tvars, tpatt, _ = Helpers.tuple (List.length args) in
      wrap [ <:match_case< $tpatt$ -> $self#nargs ctxt tvars args$ >> ]


    method case ctxt (name, args) =
      match args with
      | [] ->
	  <:match_case< $uid:name$ -> Format.pp_print_string formatter $str:name$ >>
      | _ ->
          let tvars, patt, exp = Helpers.tuple (List.length args) in
	  let format_expr =
	    <:expr< Format.pp_print_string formatter $str:name$;
                    Format.pp_print_break formatter 1 2;
                    $self#nargs ctxt tvars args$ >> in
          <:match_case< $uid:name$ $patt$ -> $in_hovbox format_expr$ >>

    method sum ?eq ctxt tname params constraints summands =
      wrap (List.map (self#case ctxt) summands)


    method field ctxt (name, ty, mut) =
      <:expr< Format.pp_print_string formatter $str:name ^ " = "$;
              $self#call_poly_expr ctxt ty "format"$ formatter $lid:name$ >>

    method record ?eq ctxt tname params constraints fields =
      let format_fields =
	List.fold_left1
          (fun l r -> <:expr< $l$; Format.pp_print_string formatter "; "; $r$ >>)
          (List.map (self#field ctxt) fields) in
      let format_record =
	<:expr<
          Format.pp_print_char formatter '{';
          $format_fields$;
          Format.pp_print_char formatter '}'; >> in
      wrap [ <:match_case< $Helpers.record_pattern fields$ -> $in_hovbox format_record$ >>]

    method polycase ctxt : Pa_deriving_common.Type.tagspec -> Ast.match_case = function
      | Type.Tag (name, []) ->
	  let format_expr =
	    <:expr< Format.pp_print_string formatter $str:"`" ^ name ^" "$ >> in
          <:match_case< `$uid:name$ -> $format_expr$ >>
      | Type.Tag (name, es) ->
	  let format_expr =
	    <:expr< Format.pp_print_string formatter $str:"`" ^ name ^" "$;
                    $self#call_expr ctxt (`Tuple es) "format"$ formatter x >> in
          <:match_case< `$uid:name$ x -> $in_hovbox format_expr$ >>
      | Type.Extends t ->
          let patt, guard, cast = Generator.cast_pattern ctxt t in
	  let format_expr =
	    <:expr< $self#call_expr ctxt t "format"$ formatter $cast$ >> in
          <:match_case< $patt$ when $guard$ -> $in_hovbox format_expr$ >>

    method variant ctxt tname params constraints (_,tags) =
      wrap (List.map (self#polycase ctxt) tags @ [ <:match_case< _ -> assert false >> ])

  end :> Generator.generator)

  let generate = Generator.generate generator
  let generate_sigs = Generator.generate_sigs generator

end

module Show = Base.Register(Description)(Builder)
