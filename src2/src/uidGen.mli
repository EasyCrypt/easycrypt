(* -------------------------------------------------------------------- *)
open Symbols

type uid = int
type uidmap

val create : unit -> uidmap
val lookup : uidmap -> symbol -> uid option
val forsym : uidmap -> symbol -> uid
