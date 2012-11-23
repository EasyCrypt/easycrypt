(* -------------------------------------------------------------------- *)
open Symbols
open Utils
open Parsetree
open Types
open Typesexpr
open Typesmod

(* -------------------------------------------------------------------- *)
type typolicy =
  | TyDecl  of symbol list
  | TyAnnot of UidGen.uidmap

val transty : Scope.scope -> typolicy -> pty -> ty

(* -------------------------------------------------------------------- *)
type epolicy = {
  epl_prob : bool;
}

val transexp : Scope.scope -> Env.env -> epolicy -> pexpr -> tyexpr * ty

(* -------------------------------------------------------------------- *)
val transsig : Scope.scope -> Env.env -> psignature -> tysig
