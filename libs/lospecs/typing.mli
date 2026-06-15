(* -------------------------------------------------------------------- *)
open Ptree
open Ast

(* -------------------------------------------------------------------- *)
module Env : sig
  type env

  val empty : env
end

type env = Env.env

(* -------------------------------------------------------------------- *)
(* Type-check a parsed lospecs program, returning each named definition
   with its elaborated body. *)
val tt_program : env -> pprogram -> (symbol * adef) list
