(* Copyright Jeremy Yallop 2007.
   This file is free software, distributed under the MIT license.
   See the file COPYING for details.
*)

open Pa_deriving_common
open Utils

module Description : Defs.ClassDescription = struct
  let classname = "Typeable"
  let runtimename = "Deriving_Typeable"
  let default_module = Some "Defaults"
  let alpha = None
  let allow_private = true
  let predefs = [
    ["int"], ["Deriving_Typeable";"int"];
    ["bool"], ["Deriving_Typeable";"bool"];
    ["unit"], ["Deriving_Typeable";"unit"];
    ["char"], ["Deriving_Typeable";"char"];
    ["int32"], ["Deriving_Typeable";"int32"];
    ["Int32";"t"], ["Deriving_Typeable";"int32"];
    ["int64"], ["Deriving_Typeable";"int64"];
    ["Int64";"t"], ["Deriving_Typeable";"int64"];
    ["nativeint"], ["Deriving_Typeable";"nativeint"];
    ["float"], ["Deriving_Typeable";"float"];
    ["num"], ["Deriving_num";"num"];
    ["string"], ["Deriving_Typeable";"string"];
    ["list"], ["Deriving_Typeable";"list"];
    ["ref"], ["Deriving_Typeable";"ref"];
    ["option"], ["Deriving_Typeable";"option"];
  ]
  let depends = []
end

module Builder(Loc : Defs.Loc) = struct

  module Helpers = Base.AstHelpers(Loc)
  module Generator = Base.Generator(Loc)(Description)

  open Loc
  open Camlp4.PreCast
  open Description

  let mkName tname =
    let file_name, sl, _, _, _, _, _, _ = Loc.to_tuple _loc in
    Printf.sprintf "%s_%d_%f_%s" file_name sl (Unix.gettimeofday ()) tname

  let wrap type_rep = [ <:str_item< let type_rep = lazy $type_rep$ >> ]

  let generator = (object(self)

    inherit Generator.generator

    method proxy () =
      None, [ <:ident< type_rep >>;
	      <:ident< has_type >>;
	      <:ident< cast >>;
	      <:ident< throwing_cast >>;
	      <:ident< make_dynamic >>;
	      <:ident< mk >>;
	    ]

    method tuple ctxt ts =
      let params =
        List.map (fun t -> <:expr< $self#call_expr ctxt t "type_rep"$ >>) ts in
      wrap <:expr< $uid:runtimename$.TypeRep.mkTuple $Helpers.expr_list params$ >>

    method gen ?eq ctxt tname params constraints =
      let paramList =
	List.fold_right
          (fun p cdr ->
            <:expr< $self#call_expr ctxt p "type_rep"$ :: $cdr$ >>)
          params
	  <:expr< [] >> in
      wrap <:expr< $uid:runtimename$.TypeRep.mkFresh $str:mkName tname$ $paramList$ >>

    method sum ?eq ctxt tname params constraints _ =
      self#gen ~eq ctxt tname params constraints
    method record ?eq ctxt tname params constraints _ =
      self#gen ~eq ctxt tname params constraints

    method variant ctxt tname params constraints (_,tags) =
      let tags, extends =
	List.fold_left
          (fun (tags, extends) -> function
            | Type.Tag (l, [])  -> <:expr< ($str:l$, None) :: $tags$ >>, extends
            | Type.Tag (l, ts) ->
		<:expr< ($str:l$, Some $self#call_expr ctxt (`Tuple ts) "type_rep"$) ::$tags$ >>,
		extends
            | Type.Extends t ->
		tags,
		<:expr< $self#call_expr ctxt t "type_rep"$::$extends$ >>)
          (<:expr< [] >>, <:expr< [] >>) tags in
      wrap <:expr< $uid:runtimename$.TypeRep.mkPolyv $tags$ $extends$ >>

  end :> Generator.generator)

  let classname = Description.classname
  let runtimename = Description.runtimename
  let generate = Generator.generate generator
  let generate_sigs = Generator.generate_sigs generator
  let generate_expr = Generator.generate_expr generator

end

module Typeable = Base.Register(Description)(Builder)

let depends = (module Builder : Defs.FullClassBuilder)
