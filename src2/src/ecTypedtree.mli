(* -------------------------------------------------------------------- *)
open EcSymbols
open EcParsetree
open EcTypes
open EcTypesexpr
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
  | UnexpectedType           of ty * ty
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
type typolicy =
    (* For type definitions bodies / operators type signatures
     * - no [Punivar] allowed
     * - each [Pvar] must appear in the constructor symbols list
     *   (assumed to contain no duplicated). [Pvar x] is replaced
     *   by [Trel i] where [i] is the index of [x] in the symbols list.
     *)
  | TyDecl of symbol list

    (* Type annotation for function parameters / result type.
     * - no [Pvar] allowed (all types are monomorphic)
     * - [Punivar] allowed (for partial type annotations, e.g. (int * _))
     *   Each [Punivar] leads to the creation of a fresh [Tunivar].
     *)
  | TyAnnot

val transty : EcEnv.env -> typolicy -> pty -> ty

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
end

(* -------------------------------------------------------------------- *)
val transsig   : EcEnv.env -> psignature -> tysig
val transtymod : EcEnv.env -> pmodule_type -> tymod
val transmod   : EcEnv.env -> EcIdent.t -> pmodule_expr -> module_expr

(* -------------------------------------------------------------------- *)
val transformula : Fenv.fenv -> pformula -> EcFol.form
