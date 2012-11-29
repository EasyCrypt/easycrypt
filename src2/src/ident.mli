(* -------------------------------------------------------------------- *)
open Symbols

(* -------------------------------------------------------------------- *)
type t = symbol * int

val create : symbol -> t
val fresh  : t -> t
val name   : t -> symbol
val stamp  : t -> UidGen.uid

(* -------------------------------------------------------------------- *)
module RawMap : Maps.Map.S with type key = t

(* -------------------------------------------------------------------- *)
module Map : sig
  type key = t

  type 'a t

  val empty   : 'a t
  val add     : key -> 'a -> 'a t -> 'a t
  val byname  : symbol -> 'a t -> 'a option
  val byident : key -> 'a t -> 'a option
end
