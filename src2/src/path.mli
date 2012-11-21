(* -------------------------------------------------------------------- *)
open Symbols

type path =
  | Pident of symbol
  | Pqname of symbol * path

val create    : string -> path
val toqsymbol : path -> qsymbol
