(* -------------------------------------------------------------------- *)
open Symbols
open Typesmod

(* -------------------------------------------------------------------- *)
type env

type ebinding = [
  | `Value  of Types.ty
  | `Module of tymod
]

val empty   : env
val bind    : symbol -> ebinding -> env -> env
val bindall : (symbol * ebinding) list -> env -> env

val bind_value  : symbol -> Types.ty -> env -> env
val bind_values : (symbol * Types.ty) list -> env -> env

val lookup_value  : qsymbol -> env -> (Path.path * Types.ty) option
val lookup_module : qsymbol -> env -> (Path.path * Typesmod.module_expr) option

