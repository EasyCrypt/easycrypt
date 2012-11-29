(* -------------------------------------------------------------------- *)
open Symbols
open Parsetree
open Types
open Typesexpr
open Typesmod

(* -------------------------------------------------------------------- *)
type typolicy =
  | TyDecl  of symbol list
  | TyAnnot of UidGen.uidmap

val transty : Env.env -> typolicy -> pty -> ty

(* -------------------------------------------------------------------- *)
type epolicy = {
  epl_prob : bool;
}

val transexp : Env.env -> epolicy -> pexpr -> tyexpr * ty

(* -------------------------------------------------------------------- *)
val transsig   : Env.env -> psignature -> tysig
val transtymod : Env.env -> pmodule_type -> tymod
val transmod   : Env.env -> Ident.t -> pmodule_expr -> module_expr
