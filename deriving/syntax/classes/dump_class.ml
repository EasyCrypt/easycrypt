(* Copyright Jeremy Yallop 2007.
   This file is free software, distributed under the MIT license.
   See the file COPYING for details.
*)

open Pa_deriving_common
open Utils

module Description : Defs.ClassDescription = struct
  let classname = "Dump"
  let runtimename = "Deriving_Dump"
  let default_module = Some "Defaults"
  let alpha = Some "Dump_alpha"
  let allow_private = false
  let predefs = [
    ["unit"], ["Deriving_Dump";"unit"];
    ["bool"], ["Deriving_Dump";"bool"];
    ["char"], ["Deriving_Dump";"char"];
    ["int"], ["Deriving_Dump";"int"];
    ["int32"], ["Deriving_Dump";"int32"];
    ["Int32";"t"], ["Deriving_Dump";"int32"];
    ["int64"], ["Deriving_Dump";"int64"];
    ["Int64";"t"], ["Deriving_Dump";"int64"];
    ["nativeint"], ["Deriving_Dump";"nativeint"];
    ["float"], ["Deriving_Dump";"float"];
    ["num"], ["Deriving_Dump";"num"];
    ["string"], ["Deriving_Dump";"string"];
    ["list"], ["Deriving_Dump";"list"];
    ["option"], ["Deriving_Dump";"option"];
  ]
  let depends = []
end

module Builder(Loc : Defs.Loc) = struct

  module Helpers = Base.AstHelpers(Loc)
  module Generator = Base.Generator(Loc)(Description)

  open Loc
  open Camlp4.PreCast
  open Description

  let wrap ?(buffer="buffer") ?(stream="stream") to_buffer from_stream =
    [ <:str_item< let to_buffer $lid:buffer$ = function $list:to_buffer$ >> ;
      <:str_item< let from_stream $lid:stream$ = $from_stream$ >> ]

  let generator = (object (self)

    inherit Generator.generator

    method proxy unit =
      None, [ <:ident< to_buffer >>;
	      <:ident< to_string >>;
	      <:ident< to_channel >>;
	      <:ident< from_stream >>;
	      <:ident< from_string >>;
	      <:ident< from_channel >>; ]

    method dump_int ctxt n =
      <:expr< $self#call_expr ctxt (`Constr (["int"],[])) "to_buffer"$
                 buffer $`int:n$ >>

    method read_int ctxt =
      <:expr< $self#call_expr ctxt (`Constr (["int"],[])) "from_stream"$ stream >>


    method nargs ctxt tvars args =
      let to_buffer id ty =
	<:expr< $self#call_expr ctxt ty "to_buffer"$ buffer $lid:id$ >> in
      let from_stream id ty e =
        <:expr< let $lid:id$ = $self#call_expr ctxt ty "from_stream"$ stream in
                $e$ >> in
      Helpers.seq_list (List.map2 to_buffer tvars args),
      (fun expr -> List.fold_right2 from_stream tvars args expr)

    method tuple ctxt tys =
      let tvars, patt, expr = Helpers.tuple (List.length tys) in
      let dumper, undump = self#nargs ctxt tvars tys in
      wrap [ <:match_case< $patt$ -> $dumper$ >> ] (undump expr)

    method case ctxt (ctor,args) n =
      match args with
      | [] ->
	  <:match_case< $uid:ctor$ -> $self#dump_int ctxt n$ >>,
          <:match_case< $`int:n$ -> $uid:ctor$ >>
      | _ ->
        let tvars, patt, expr = Helpers.tuple (List.length args) in
	let expr = <:expr< $uid:ctor$ $expr$ >> in
        let dumper, undumper = self#nargs ctxt tvars args in
	<:match_case< $uid:ctor$ $patt$ -> $self#dump_int ctxt n$; $dumper$ >>,
	<:match_case< $`int:n$ -> $undumper expr$ >>

    method sum ?eq ctxt tname params constraints summands =
      let msg = "Dump: unexpected tag %d at character %d when deserialising " ^ tname in
      let dumpers, undumpers = List.split (List.mapn (self#case ctxt) summands) in
      let undumpers =
        <:expr< match $self#read_int ctxt$ with
	        $list:undumpers$
                | n -> raise ($uid:runtimename$.$uid:classname^ "_error"$
				(Printf.sprintf $str:msg$ n (Stream.count stream))) >>
      in
      wrap dumpers undumpers


    method field ctxt (name, ty, mut) =
      if mut = `Mutable then
        raise (Base.Underivable
		 (classname ^ " cannot be derived for record types "
		  ^ " with mutable fields (" ^ name ^ ")"));
      <:expr< $self#call_poly_expr ctxt ty "to_buffer"$ buffer $lid:name$ >>,
      <:binding< $lid:name$ = $self#call_poly_expr ctxt ty "from_stream"$ stream >>

    method record ?eq ctxt tname params constraints fields =
       let dumpers, undumpers = List.split (List.map (self#field ctxt) fields) in
       let bind b e = <:expr< let $b$ in $e$ >> in
       let undump = List.fold_right bind undumpers (Helpers.record_expression fields) in
       let dumper =
	 <:match_case<
	   $Helpers.record_pattern fields$
	   -> $Helpers.seq_list dumpers$
         >>
       in
       wrap [dumper] undump


    method polycase ctxt tagspec n : Ast.match_case * Ast.match_case =
      match tagspec with
      | Type.Tag (name, []) ->
	    <:match_case< `$name$ -> $self#dump_int ctxt n$ >>,
            <:match_case< $`int:n$ -> `$name$ >>
      | Type.Tag (name, es) ->
	    let to_buffer =
	      <:expr< $self#call_expr ctxt (`Tuple es) "to_buffer"$ buffer x >> in
	    let from_stream =
	      <:expr< $self#call_expr ctxt (`Tuple es) "from_stream"$ stream >> in
	    <:match_case< `$name$ x -> $self#dump_int ctxt n$; $to_buffer$ >>,
            <:match_case< $`int:n$ -> `$name$ ($from_stream$) >>
      | Type.Extends t ->
          let patt, guard, cast = Generator.cast_pattern ctxt t in
	  let to_buffer =
	    <:expr< $self#call_expr ctxt t "to_buffer"$ buffer $cast$ >> in
	  let from_stream =
	    <:expr< $self#call_expr ctxt t "from_stream"$ stream >> in
          <:match_case< $patt$ when $guard$ -> $self#dump_int ctxt n$; $to_buffer$ >>,
          <:match_case< $`int:n$ -> ($from_stream$ :> a) >>

    method variant ctxt tname params constraints (_, tags) =
      let msg = "Dump: unexpected tag %d at character %d "
	        ^ "when deserialising polymorphic variant" in
      let dumpers, undumpers = List.split (List.mapn (self#polycase ctxt) tags) in
      let undumpers =
        <:expr< match $self#read_int ctxt$ with
	        $list:undumpers$
                | n -> raise ($uid:runtimename$.$uid:classname^ "_error"$
                                (Printf.sprintf $str:msg$ n (Stream.count stream))) >>
      in
      wrap (dumpers @ [ <:match_case< _ -> assert false >>]) undumpers

  end :> Generator.generator)

  let generate = Generator.generate generator
  let generate_sigs = Generator.generate_sigs generator

end

module Dump = Base.Register(Description)(Builder)
