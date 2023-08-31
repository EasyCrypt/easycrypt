(* -------------------------------------------------------------------- *)
open EcIdent
open EcSymbols
open EcTypes
open EcModules

(* -------------------------------------------------------------------- *)
type senv

(* -------------------------------------------------------------------- *)
module Env : sig
  val empty : EcEnv.env -> senv
  val fresh : senv -> symbol -> senv * ident
end

(* -------------------------------------------------------------------- *)
exception SemNotSupported

(* -------------------------------------------------------------------- *)
type mode = [`Det | `Distr]

(* -------------------------------------------------------------------- *)
val translate_e : senv -> expr -> expr
val translate_s : senv -> (senv -> mode * expr) -> stmt -> mode * expr
