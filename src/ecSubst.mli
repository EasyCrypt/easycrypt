(* -------------------------------------------------------------------- *)
open EcTypesmod
open EcTypes
open EcTypesmod
open EcDecl
open EcFol

(* -------------------------------------------------------------------- *)
type subst

type subst1 = [
  | `Path  of EcPath.path
  | `Local of EcIdent.t
]

exception SubstNameClash of EcIdent.t
exception InconsistentSubst

val empty   : subst
val add     : subst -> EcIdent.t -> subst1 -> subst
val create  : (EcIdent.t * subst1) list -> subst
val compose : subst -> subst -> subst

(* -------------------------------------------------------------------- *)
val subst_path  : subst -> EcPath.path -> EcPath.path
val subst_local : subst -> EcIdent.t -> EcIdent.t

(* -------------------------------------------------------------------- *)
val subst_ty : subst -> ty -> ty
val subst_tyexpr : subst -> tyexpr -> tyexpr
val subst_form : subst -> form -> form
val subst_tydecl : subst -> tydecl -> tydecl
val subst_op : subst -> operator -> operator
val subst_tysig : subst -> tysig -> tysig
val subst_modtype : subst -> tymod -> tymod
val subst_theory : subst -> EcPath.path -> theory -> theory
