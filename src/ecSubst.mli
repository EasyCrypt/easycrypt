(* -------------------------------------------------------------------- *)
open EcSymbols
open EcPath
open EcTypesmod
open EcTypes
open EcTypesmod
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
val subst_path   : subst -> path   -> path
val subst_mcpath : subst -> mcpath -> mcpath
val subst_mpath  : subst -> mpath  -> mpath
val subst_xpath  : subst -> xpath  -> xpath
val subst_local  : subst -> EcIdent.t -> EcIdent.t

(* -------------------------------------------------------------------- *)
val subst_ty     : subst -> ty -> ty
val subst_tyexpr : subst -> tyexpr -> tyexpr
val subst_form   : subst -> form -> form
val subst_tydecl : subst -> tydecl -> tydecl
val subst_op     : subst -> operator -> operator
val subst_theory : subst -> EcPath.path -> theory -> theory

(* -------------------------------------------------------------------- *)
val subst_modsig_comps : subst -> module_sig_comps -> module_sig_comps
val subst_modsig_desc  : subst -> module_sig_desc -> module_sig_desc
val subst_modsig_body  : subst -> module_sig_body -> module_sig_body

val subst_modtype      : subst -> module_type -> module_type
val subst_modtype_desc : subst -> module_type_desc -> module_type_desc

val subst_module_comps : subst -> EcPath.path -> module_comps -> module_comps
