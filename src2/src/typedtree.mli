(* -------------------------------------------------------------------- *)
open Symbols
open Utils
open Parsetree
open Types

(* -------------------------------------------------------------------- *)
type local = symbol * int

type tyexpr =
  | Eunit                                   (* unit literal      *)
  | Ebool   of bool                         (* bool literal      *)
  | Eint    of int                          (* int. literal      *)
  | Elocal  of local * ty                   (* local variable    *)
  | Eident  of Path.path * ty               (* symbol            *)
  | Eapp    of Path.path * tyexpr list      (* op. application   *)
  | Elet    of lpattern * tyexpr * tyexpr   (* let binding       *)
  | Etuple  of tyexpr list                  (* tuple constructor *)
  | Eif     of tyexpr * tyexpr * tyexpr     (* _ ? _ : _         *)
  | Ernd    of tyrexpr                      (* random expression *)

and tyrexpr =
  | Rbool                                   (* flip               *)
  | Rinter    of tyexpr * tyexpr            (* interval sampling  *)
  | Rbitstr   of tyexpr                     (* bitstring sampling *)
  | Rexcepted of tyrexpr * tyexpr           (* restriction        *)
  | Rapp      of Path.path * tyexpr list    (* p-op. application  *)

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
