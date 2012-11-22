(* -------------------------------------------------------------------- *)
open Symbols
open Utils
open Parsetree
open Types

(* -------------------------------------------------------------------- *)
type typolicy =
  | TyDecl  of symbol list
  | TyAnnot of UidGen.uidmap

val transty : Scope.scope -> typolicy -> pty -> ty

(* -------------------------------------------------------------------- *)
module Env : sig
  type env

  val empty   : env
  val bind    : symbol * ty -> env -> env
  val bindall : (symbol * ty) list -> env -> env
end
  
(* -------------------------------------------------------------------- *)
type epolicy = {
  epl_prob : bool;
}

val transexp : Scope.scope -> Env.env -> epolicy -> pexpr -> tyexpr * ty
