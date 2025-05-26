(* -------------------------------------------------------------------- *)
open EcIdent
open EcPath
open EcAst
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

val empty : subst
val is_empty : subst -> bool

(* -------------------------------------------------------------------- *)
val add_module   : subst -> EcIdent.t -> mpath -> subst
val add_path     : subst -> src:path -> dst:path -> subst
val add_tydef    : subst -> path -> (EcIdent.t list * ty) -> subst
val add_opdef    : subst -> path -> (EcIdent.t list * expr) -> subst
val add_pddef    : subst -> path -> (EcIdent.t list * form) -> subst
val add_moddef   : subst -> src:path -> dst:mpath -> subst (* Only concrete modules *)
val add_memory   : subst -> EcIdent.t -> EcIdent.t -> subst

val add_flocal : subst -> EcIdent.t -> form -> subst
val add_elocals : subst -> EcIdent.t list -> expr list -> subst
val rename_flocal : subst -> EcIdent.t -> EcIdent.t -> ty -> subst

(* -------------------------------------------------------------------- *)
val freshen_type : (ty_params * ty) -> (ty_params * ty)

(* -------------------------------------------------------------------- *)
val subst_theory  : subst -> theory -> theory
val subst_ax      : subst -> axiom -> axiom
val subst_op      : subst -> operator -> operator
val subst_tydecl  : subst -> tydecl -> tydecl
val subst_tc      : subst -> typeclass -> typeclass
val subst_theory  : subst -> theory -> theory
val subst_branches : subst -> opbranches -> opbranches

(* -------------------------------------------------------------------- *)
val subst_path         : subst -> path  -> path
val subst_mpath        : subst -> mpath -> mpath
val subst_xpath        : subst -> xpath -> xpath
val subst_function     : subst -> function_ -> function_
val subst_module       : subst -> module_expr -> module_expr
val subst_top_module   : subst -> top_module_expr -> top_module_expr
val subst_module_comps : subst -> module_comps -> module_comps
val subst_module_body  : subst -> module_body -> module_body
val subst_modtype      : subst -> module_type -> module_type
val subst_modsig       : ?params:(ident list) -> subst -> module_sig -> module_sig
val subst_top_modsig   : subst -> top_module_sig -> top_module_sig
val subst_modsig_body  : subst -> module_sig_body -> module_sig_body
val subst_mod_restr    : subst -> mod_restr -> mod_restr
val subst_oracle_infos : subst -> oracle_infos -> oracle_infos

(* -------------------------------------------------------------------- *)
val subst_gty   : subst -> gty -> gty
val subst_genty : subst -> (ty_params * ty) -> (ty_params * ty)
val subst_ty    : subst -> ty   -> ty
val subst_form  : subst -> form -> form
val subst_expr  : subst -> expr -> expr
val subst_stmt  : subst -> stmt -> stmt

val subst_progvar : subst -> prog_var -> prog_var
val subst_mem : subst -> EcIdent.t -> EcIdent.t
val subst_flocal : subst -> form -> form

(* -------------------------------------------------------------------- *)
val open_oper : operator -> ty list -> ty * operator_kind
val open_tydecl : tydecl -> ty list -> ty_body
