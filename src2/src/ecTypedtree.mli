(* -------------------------------------------------------------------- *)
open EcSymbols
open EcParsetree
open EcTypes
open EcTypesexpr
open EcTypesmod

(* -------------------------------------------------------------------- *)
type typolicy =
  | TyDecl  of symbol list
  | TyAnnot of EcUidgen.uidmap

val transty : EcEnv.env -> typolicy -> pty -> ty

(* -------------------------------------------------------------------- *)
type epolicy = {
  epl_prob : bool;
}

val transexp : EcEnv.env -> epolicy -> pexpr -> tyexpr * ty

(* -------------------------------------------------------------------- *)
module Fenv : sig 
  type fenv
  val mono_fenv : EcEnv.env -> fenv
end
val transformula : Fenv.fenv -> pformula -> EcFol.form
(* -------------------------------------------------------------------- *)
val transsig   : EcEnv.env -> psignature -> tysig
val transtymod : EcEnv.env -> pmodule_type -> tymod
val transmod   : EcEnv.env -> EcIdent.t -> pmodule_expr -> module_expr
