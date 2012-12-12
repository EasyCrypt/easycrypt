(* -------------------------------------------------------------------- *)
open EcSymbols

(* -------------------------------------------------------------------- *)
type t = symbol * int

val create : symbol -> t
val fresh  : t -> t
val name   : t -> symbol
val stamp  : t -> EcUidgen.uid

(* -------------------------------------------------------------------- *)
module RawMap : EcMaps.Map.S with type key = t

(* -------------------------------------------------------------------- *)
module Map : sig
  type key = t

  type 'a t

  val empty     : 'a t
  val add       : key -> 'a -> 'a t -> 'a t
  val allbyname : symbol -> 'a t -> 'a list
  val byname    : symbol -> 'a t -> 'a option
  val byident   : key -> 'a t -> 'a option
  val update    : key -> ('a -> 'a) -> 'a t -> 'a t
  val merge     : 'a t -> 'a t -> 'a t
end

module Mid : EcMaps.Map.S with type key = t
module Sid : Set.S with type elt = t
module Hid : Hashtbl.S with type key = t
