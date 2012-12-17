(* -------------------------------------------------------------------- *)
open EcSymbols
open EcParsetree
open EcTypes
open EcDecl
open EcTypesmod

(* -------------------------------------------------------------------- *)
type tyerror =
  | UnknownVariable          of qsymbol
  | UnknownFunction          of qsymbol
  | UnknownTypeName          of qsymbol
  | UnknownOperatorForSig    of qsymbol * ty list
  | InvalidNumberOfTypeArgs  of qsymbol * int * int
  | ApplInvalidArity
  | UnboundTypeParameter     of symbol
  | OpNotOverloadedForSig    of qsymbol * ty list
  | UnexpectedType           of ty * ty * ty * ty
  | NonLinearPattern         of lpattern
  | DuplicatedLocals
  | ProbaExpressionForbidden
  | PatternForbiden
  | ModApplToNonFunctor
  | ModApplInvalidArity
  | ModApplInvalidArgInterface
  | PropExpected of pformula
  | TermExpected of pformula

exception TyError of Location.t * tyerror

(* -------------------------------------------------------------------- *)
module TyPolicy : sig 
  type t
  val decl  : t -> EcIdent.t list
  val relax : t -> t 
  val empty : t 
  val init  : string list option -> t
end

(* -------------------------------------------------------------------- *)
val transty : EcEnv.env -> TyPolicy.t -> pty -> ty * TyPolicy.t
val transtys : EcEnv.env -> TyPolicy.t -> pty list -> ty list * TyPolicy.t
val transty_notv : EcEnv.env -> pty -> ty 

(* -------------------------------------------------------------------- *)
val select_op :
     proba:bool
  -> EcEnv.env
  -> qsymbol
  -> EcUnify.unienv
  -> ty list
  -> (EcPath.path * operator * ty * EcUnify.unienv) list

(* -------------------------------------------------------------------- *)
type epolicy = {
  epl_prob : bool;
}

(* [transexp env policy ue pe] translates the *parsed* expression [pe]
 * to a *typed* expression, under environment [env], using policy
 * [policy], and unification map [ue].
*)
val transexp : EcEnv.env -> epolicy -> EcUnify.unienv -> pexpr -> tyexpr * ty
val transexpcast :
    EcEnv.env -> epolicy -> EcUnify.unienv -> ty -> pexpr -> tyexpr

(* -------------------------------------------------------------------- *)
module Fenv : sig 
  type fenv
  val mono_fenv : EcEnv.env -> fenv
  val bind_locals : fenv -> EcIdent.t list -> ty list -> fenv
end
val transformula : Fenv.fenv -> TyPolicy.t -> EcUnify.unienv -> 
  pformula -> EcFol.form * EcUnify.unienv

(* -------------------------------------------------------------------- *)
val transsig   : EcEnv.env -> psignature -> tysig
val transtymod : EcEnv.env -> pmodule_type -> tymod
val transmod   : EcEnv.env -> EcIdent.t -> pmodule_expr -> module_expr
