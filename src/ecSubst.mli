(* -------------------------------------------------------------------- *)
open EcSymbols
open EcPath
open EcTypesmod
open EcTypes
open EcTheory
open EcDecl
open EcFol

(* -------------------------------------------------------------------- *)
type subst_name_clash = [
  | `Ident of EcIdent.t
]

exception SubstNameClash of subst_name_clash
exception InconsistentSubst

(* -------------------------------------------------------------------- *)
type subst

val empty      : subst
val add_module : subst -> EcIdent.t -> mpath -> subst

(* -------------------------------------------------------------------- *)
val is_empty   : subst -> bool
(* -------------------------------------------------------------------- *)
val subst_path  : subst -> EcPath.path -> EcPath.path
val subst_mpath : subst -> EcPath.mpath -> EcPath.mpath

(* -------------------------------------------------------------------- *)
val subst_pvar : subst -> prog_var -> prog_var
val subst_ty : subst -> ty -> ty
val subst_tyexpr : subst -> tyexpr -> tyexpr
val subst_form : subst -> form -> form
val subst_tydecl : subst -> tydecl -> tydecl
val subst_op : subst -> operator -> operator
val subst_theory : subst -> theory -> theory

(* -------------------------------------------------------------------- *)
val subst_function     : subst -> function_ -> function_ 
val subst_module       : subst -> module_expr -> module_expr
val subst_module_comps : subst -> module_comps -> module_comps
val subst_modtype      : subst -> module_type -> module_type
val subst_modsig       : subst -> module_sig -> module_sig
val subst_modsig_body  : subst -> module_sig_body -> module_sig_body
