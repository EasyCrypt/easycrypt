(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcMaps
open EcSymbols

(* -------------------------------------------------------------------- *)
type ident = private {
  id_symb : symbol;
  id_tag  : int;
}

type idents = ident list

type t = ident

val create   : symbol -> t
val fresh    : t -> t
val name     : t -> symbol
val tag      : t -> int
val tostring : t -> string

(* -------------------------------------------------------------------- *)
val id_equal : t -> t -> bool
val id_compare : t -> t -> int
val id_hash : t -> int

(* -------------------------------------------------------------------- *)
module Mid : Map.S with type key = t
module Sid : Set.S with module M = Map.MakeBase(Mid)
module Hid : EcMaps.EHashtbl.S with type key = ident

(* -------------------------------------------------------------------- *)
val fv_singleton : ident -> int Mid.t
val fv_union     : int Mid.t -> int Mid.t -> int Mid.t
val fv_diff      : int Mid.t -> 'a Mid.t -> int Mid.t
val fv_add       : ident -> int Mid.t -> int Mid.t

(* -------------------------------------------------------------------- *)
val pp_ident : Format.formatter -> t -> unit
