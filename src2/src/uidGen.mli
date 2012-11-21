(* -------------------------------------------------------------------- *)
open Symbols

(* -------------------------------------------------------------------- *)
val unique : unit -> int

(* -------------------------------------------------------------------- *)
type uid = int
type uidmap

val create : unit -> uidmap
val lookup : uidmap -> symbol -> uid option
val forsym : uidmap -> symbol -> uid
