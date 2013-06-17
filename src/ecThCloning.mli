(* -------------------------------------------------------------------- *)
open EcSymbols
open EcParsetree
open EcEnv

(* -------------------------------------------------------------------- *)
type ovkind =
| OVK_Type
| OVK_Operator
| OVK_Predicate

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
val clone : EcEnv.env -> theory_cloning -> symbol * ctheory_w3
