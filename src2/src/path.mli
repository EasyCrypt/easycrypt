(* -------------------------------------------------------------------- *)
open Symbols

type path =
  | Pident of symbol
  | Pqname of symbol * path

val create    : string -> path
val toqsymbol : path -> qsymbol

val path_equal : path -> path -> bool

module Mp : Map.S with type key = path

type subst_path 
val mk_subst : path -> path -> subst_path
val subst_path : subst_path -> path -> path
