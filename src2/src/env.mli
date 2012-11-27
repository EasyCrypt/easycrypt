(* -------------------------------------------------------------------- *)
open Symbols
open Typesmod

(* -------------------------------------------------------------------- *)
type env

exception LookupFailure

(* -------------------------------------------------------------------- *)
val empty : env

(* -------------------------------------------------------------------- *)
val bind_variable   : Ident.t -> Types.ty -> env -> env
val bind_variables  : (Ident.t * Types.ty) list -> env -> env
val lookup_variable : qsymbol -> env -> Path.path * Types.ty

(* -------------------------------------------------------------------- *)
val bind_function   : Ident.t -> funsig -> env -> env
val bind_functions  : (Ident.t * funsig) list -> env -> env
val lookup_function : qsymbol -> env -> Path.path * funsig

(* -------------------------------------------------------------------- *)
val bind_module   : Ident.t -> tymod -> env -> env
val bind_modules  : (Ident.t * tymod) list -> env -> env
val lookup_module : qsymbol -> env -> Path.path * Typesmod.tymod

(* -------------------------------------------------------------------- *)
type ebinding = [
  | `Variable  of Types.ty
  | `Function  of funsig
  | `Module    of tymod
]

val bind1   : Ident.t * ebinding -> env -> env
val bindall : (Ident.t * ebinding) list -> env -> env
