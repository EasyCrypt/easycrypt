(* -------------------------------------------------------------------- *)
open EcLocation
open EcSymbols
open EcParsetree

(* -------------------------------------------------------------------- *)
type incompatible =
| NotSameNumberOfTyParam of int * int
| DifferentType of EcTypes.ty * EcTypes.ty
| OpBody (* of (EcPath.path * EcDecl.operator) * (EcPath.path * EcDecl.operator) *)
| TyBody (* of (EcPath.path * EcDecl.tydecl) * (EcPath.path * EcDecl.tydecl) *)

type ovkind =
| OVK_Type
| OVK_Operator
| OVK_Predicate
| OVK_Abbrev
| OVK_Theory
| OVK_Lemma
| OVK_ModType

type clone_error =
| CE_UnkTheory         of qsymbol
| CE_DupOverride       of ovkind * qsymbol
| CE_UnkOverride       of ovkind * qsymbol
| CE_ThyOverride       of qsymbol
| CE_UnkAbbrev         of qsymbol
| CE_TypeArgMism       of ovkind * qsymbol
| CE_OpIncompatible    of qsymbol * incompatible
| CE_PrIncompatible    of qsymbol * incompatible
| CE_TyIncompatible    of qsymbol * incompatible
| CE_ModTyIncompatible of qsymbol
| CE_ModIncompatible   of qsymbol
| CE_InvalidRE         of string
| CE_InlinedOpIsForm   of qsymbol
| CE_ProofForLemma     of qsymbol

exception CloneError of EcEnv.env * clone_error

val clone_error : EcEnv.env -> clone_error -> 'a

(* -------------------------------------------------------------------- *)
type evclone = {
  evc_types    : (ty_override located) Msym.t;
  evc_ops      : (op_override located) Msym.t;
  evc_preds    : (pr_override located) Msym.t;
  evc_abbrevs  : (nt_override located) Msym.t;
  evc_modexprs : (me_override located) Msym.t;
  evc_modtypes : (mt_override located) Msym.t;
  evc_lemmas   : evlemma;
  evc_ths      : evclone Msym.t;
}

and evlemma = {
  ev_global  : (ptactic_core option * evtags option) list;
  ev_bynames : evinfo Msym.t;
}

and evtags = ([`Include | `Exclude] * symbol) list
and evinfo = ptactic_core option * clmode * bool (* explicit *)

val evc_empty : evclone

(* -------------------------------------------------------------------- *)
type axclone = {
  axc_axiom : symbol * EcDecl.axiom;
  axc_path  : EcPath.path;
  axc_env   : EcSection.scenv;
  axc_tac   : EcParsetree.ptactic_core option;
}

(* -------------------------------------------------------------------- *)
type clone = {
  cl_name   : symbol;
  cl_theory : EcPath.path * EcEnv.Theory.t;
  cl_clone  : evclone;
  cl_rename : renaming list;
  cl_ntclr  : EcPath.Sp.t;
}

and renaming_kind = [
  | `All
  | `Selected of rk_categories
]

and renaming =
  renaming_kind * (EcRegexp.regexp * EcRegexp.subst)

and rk_categories = {
  rkc_lemmas  : bool;
  rkc_ops     : bool;
  rkc_preds   : bool;
  rkc_types   : bool;
  rkc_module  : bool;
  rkc_modtype : bool;
  rkc_theory  : bool;
}

(* -------------------------------------------------------------------- *)
val rename : renaming -> theory_renaming_kind * string -> string option
val clone  : EcSection.scenv -> theory_cloning -> clone
