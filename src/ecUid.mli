(* -------------------------------------------------------------------- *)
open EcMaps
open EcSymbols

(* -------------------------------------------------------------------- *)
val unique : unit -> int

module type ICore = sig
  type uid

  (* ------------------------------------------------------------------ *)
  val unique      : unit -> uid
  val uid_equal   : uid -> uid -> bool
  val uid_compare : uid -> uid -> int

  (* ------------------------------------------------------------------ *)
  module Muid : Map.S  with type key = uid
  module Suid : Set.S  with module M = Map.MakeBase(Muid)

  (* ------------------------------------------------------------------ *)
  module SMap : sig
    type uidmap

    val create : unit -> uidmap
    val lookup : uidmap -> symbol -> uid option
    val forsym : uidmap -> symbol -> uid
    val pp_uid : Format.formatter -> uid -> unit
  end
end

(* -------------------------------------------------------------------- *)
type uid = int

(* -------------------------------------------------------------------- *)
include ICore with type uid := uid

(* -------------------------------------------------------------------- *)
module CoreGen() : ICore with type uid = private uid

(* -------------------------------------------------------------------- *)
module NameGen : sig
  type t

  val ofint  : int -> string
  val bulk   : ?fmt:(string -> string) -> int -> string list
  val create : unit -> t
  val get    : t -> uid -> string
end
