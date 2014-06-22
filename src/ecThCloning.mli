(* Copyright (c) - 2012-2014 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-B license *)

(* -------------------------------------------------------------------- *)
open EcSymbols
open EcParsetree
open EcEnv

(* -------------------------------------------------------------------- *)
type ovkind =
| OVK_Type
| OVK_Operator
| OVK_Predicate
| OVK_Theory
| OVK_Lemma

type clone_error =
| CE_DupOverride    of ovkind * qsymbol
| CE_UnkOverride    of ovkind * qsymbol
| CE_CrtOverride    of ovkind * qsymbol
| CE_TypeArgMism    of ovkind * qsymbol
| CE_OpIncompatible of qsymbol
| CE_PrIncompatible of qsymbol

exception CloneError of EcEnv.env * clone_error

val clone_error : EcEnv.env -> clone_error -> 'a

(* -------------------------------------------------------------------- *)
type axclone = {
  axc_axiom : symbol * EcDecl.axiom;
  axc_path  : EcPath.path;
  axc_env   : EcEnv.env;
  axc_tac   : EcParsetree.ptactic_core option;
}

val clone : EcEnv.env -> theory_cloning -> symbol * axclone list * ctheory_w3
