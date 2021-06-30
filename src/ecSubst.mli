(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcIdent
open EcPath
open EcModules
open EcTypes
open EcTheory
open EcDecl
open EcCoreFol

(* -------------------------------------------------------------------- *)
type subst_name_clash = [
  | `Ident of EcIdent.t
]

exception SubstNameClash of subst_name_clash
exception InconsistentSubst

(* -------------------------------------------------------------------- *)
type subst

val empty      : subst
val is_empty   : subst -> bool

(* -------------------------------------------------------------------- *)
val add_module : subst -> EcIdent.t -> mpath -> subst
val add_path   : subst -> src:path -> dst:path -> subst
val add_tydef  : subst -> path -> (EcIdent.t list * ty) -> subst
val add_opdef  : subst -> path -> (EcIdent.t list * expr) -> subst
val add_pddef  : subst -> path -> (EcIdent.t list * form) -> subst

(* -------------------------------------------------------------------- *)
val freshen_type : (ty_params * ty) -> (ty_params * ty)

(* -------------------------------------------------------------------- *)
val subst_theory  : subst -> theory -> theory
val subst_ax      : subst -> axiom -> axiom
val subst_op      : subst -> operator -> operator
val subst_tydecl  : subst -> tydecl -> tydecl
val subst_tc      : subst -> typeclass -> typeclass
val subst_ctheory : subst -> ctheory -> ctheory

(* -------------------------------------------------------------------- *)
val subst_path         : subst -> path  -> path
val subst_mpath        : subst -> mpath -> mpath
val subst_function     : subst -> function_ -> function_
val subst_module       : subst -> module_expr -> module_expr
val subst_module_comps : subst -> module_comps -> module_comps
val subst_module_body  : subst -> module_body -> module_body
val subst_modtype      : subst -> module_type -> module_type
val subst_modsig       : ?params:(ident list) -> subst -> module_sig -> module_sig
val subst_modsig_body  : subst -> module_sig_body -> module_sig_body

(* -------------------------------------------------------------------- *)
val subst_genty : subst -> (ty_params * ty) -> (ty_params * ty)
val subst_ty    : subst -> ty   -> ty
val subst_form  : subst -> form -> form

(* -------------------------------------------------------------------- *)
val open_oper : operator -> ty list -> ty * operator_kind
val open_tydecl : tydecl -> ty list -> ty_body
