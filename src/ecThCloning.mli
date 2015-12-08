(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2015 - IMDEA Software Institute
 * Copyright (c) - 2012--2015 - Inria
 * 
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcLocation
open EcSymbols
open EcParsetree

(* -------------------------------------------------------------------- *)
type incompatible =
| NotSameNumberOfTyParam of int * int 
| DifferentType of EcTypes.ty * EcTypes.ty

type ovkind =
| OVK_Type
| OVK_Operator
| OVK_Predicate
| OVK_Theory
| OVK_Lemma

type clone_error =
| CE_UnkTheory      of qsymbol
| CE_DupOverride    of ovkind * qsymbol
| CE_UnkOverride    of ovkind * qsymbol
| CE_CrtOverride    of ovkind * qsymbol
| CE_UnkAbbrev      of qsymbol
| CE_TypeArgMism    of ovkind * qsymbol
| CE_OpIncompatible of qsymbol * incompatible
| CE_PrIncompatible of qsymbol * incompatible
| CE_InvalidRE      of string

exception CloneError of EcEnv.env * clone_error

val clone_error : EcEnv.env -> clone_error -> 'a

(* -------------------------------------------------------------------- *)
type evclone = {
  evc_types  : (ty_override located) Msym.t;
  evc_ops    : (op_override located) Msym.t;
  evc_preds  : (pr_override located) Msym.t;
  evc_lemmas : evlemma;
  evc_ths    : evclone Msym.t;
}

and evlemma = {
  ev_global  : (ptactic_core option * Ssym.t option) list;
  ev_bynames : (ptactic_core option) Msym.t;
}

val evc_empty : evclone

(* -------------------------------------------------------------------- *)
type axclone = {
  axc_axiom : symbol * EcDecl.axiom;
  axc_path  : EcPath.path;
  axc_env   : EcEnv.env;
  axc_tac   : EcParsetree.ptactic_core option;
}

(* -------------------------------------------------------------------- *)
type clone = {
  cl_name   : symbol;
  cl_theory : EcPath.path * (EcEnv.Theory.t * EcTheory.thmode);
  cl_clone  : evclone;
  cl_rename : renaming list;
  cl_ntclr  : EcPath.Sp.t;
}

and renaming_kind = [
  | `All
  | `Selected of rk_categories
]

and renaming =
  renaming_kind * (Pcre.regexp * Pcre.substitution)

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

val clone : EcEnv.env -> theory_cloning -> clone
