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
val uid_equal : uid -> uid -> bool

module Muid : Map.S with type key = uid
module Suid : Set.S with type elt = uid

(* -------------------------------------------------------------------- *)
module NameGen : sig
  type t

  val ofint  : int -> string
  val create : unit -> t
  val get    : t -> uid -> string
end

