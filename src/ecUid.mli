(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2014 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcMaps
open EcSymbols

(* -------------------------------------------------------------------- *)
val unique : unit -> int

(* -------------------------------------------------------------------- *)
type uid = int
type uidmap

val create : unit -> uidmap
val lookup : uidmap -> symbol -> uid option
val forsym : uidmap -> symbol -> uid

(* -------------------------------------------------------------------- *)
val uid_equal   : uid -> uid -> bool
val uid_compare : uid -> uid -> int

module Muid : Map.S  with type key = uid
module Suid : Set.S  with module M = Map.MakeBase(Muid)

(* -------------------------------------------------------------------- *)
module NameGen : sig
  type t

  val ofint  : int -> string
  val create : unit -> t
  val get    : t -> uid -> string
end
