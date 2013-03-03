(* -------------------------------------------------------------------- *)
open EcSymbols
open EcParsetree
open EcTypes
open EcDecl
open EcModules

(* -------------------------------------------------------------------- *)
type tyerror =
  | UnknownVariable          of qsymbol
  | UnknownFunction          of qsymbol
  | UnknownTypeName          of qsymbol
  | UnknownTyModName         of qsymbol
  | UnknownModName           of qsymbol
  | UnknownOperatorForSig    of qsymbol * ty list
  | InvalidNumberOfTypeArgs  of qsymbol * int * int
  | ApplInvalidArity
  | UnboundTypeParameter     of symbol
  | OpNotOverloadedForSig    of qsymbol * ty list
  | UnexpectedType           of ty * ty * ty * ty
  | NonLinearPattern         of lpattern
  | DuplicatedLocals         of psymbol option
  | ProbaExpressionForbidden
  | PatternForbiden
  | ModApplToNonFunctor
  | ModApplInvalidArity
  | ModApplInvalidArgInterface
  | UnificationVariableNotAllowed
  | TypeVariableNotAllowed
  | RandomExprNotAllowed
  | UnNamedTypeVariable
  | UnusedTypeVariable

exception TyError of tyerror

val tyerror : EcLocation.t -> tyerror -> 'a

(* -------------------------------------------------------------------- *)
type typolicy
val tp_tydecl : typolicy
val tp_relax  : typolicy

(* -------------------------------------------------------------------- *)
val transty : typolicy -> EcEnv.env -> EcUnify.unienv -> pty -> ty 
val transtys :  
    typolicy -> EcEnv.env -> EcUnify.unienv -> pty list -> ty list

val transtvi : EcEnv.env -> EcUnify.unienv -> tvar_inst -> EcUnify.UniEnv.tvi

(* -------------------------------------------------------------------- *)
val transexp : EcEnv.env -> EcUnify.unienv -> pexpr -> tyexpr * ty
val transexpcast : EcEnv.env -> EcUnify.unienv -> ty -> pexpr -> tyexpr

(* -------------------------------------------------------------------- *)
module Fenv : sig 
  type fenv
  val mono_fenv : EcEnv.env -> fenv
  val bind_locals : fenv -> EcIdent.t list -> ty list -> fenv
  val fenv_hyps : EcEnv.env -> EcFol.hyps -> fenv
end

val transformula : Fenv.fenv -> EcUnify.unienv -> pformula -> EcFol.form 
val transform    : Fenv.fenv -> EcUnify.unienv -> pformula -> ty -> EcFol.form

(* -------------------------------------------------------------------- *)
val transmodsig  : EcEnv.env -> symbol -> pmodule_sig  -> module_sig
val transmodtype : EcEnv.env -> pmodule_type -> module_type * module_sig
val transmod     : EcEnv.env -> symbol -> pmodule_expr -> module_expr

(* -------------------------------------------------------------------- *)
val check_tymod_sub : EcEnv.env -> module_sig -> module_sig -> unit
val check_tymod_eq  : EcEnv.env -> module_sig -> module_sig -> unit

(* -------------------------------------------------------------------- *)
val e_inuse : tyexpr -> EcPath.Sm.t
val i_inuse : instr  -> use_flags EcPath.Mm.t
val s_inuse : stmt   -> use_flags EcPath.Mm.t
