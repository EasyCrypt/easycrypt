(* -------------------------------------------------------------------- *)
open Symbols

(* -------------------------------------------------------------------- *)
type path =
  | Pident of Ident.t
  | Pqname of path * Ident.t

val equal : path -> path -> bool

(* -------------------------------------------------------------------- *)
val create    : string -> path
val toqsymbol : path -> qsymbol

(* -------------------------------------------------------------------- *)
module Mp : Map.S with type key = path
