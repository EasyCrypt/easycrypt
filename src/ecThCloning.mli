(* -------------------------------------------------------------------- *)
open EcSymbols
open EcParsetree
open EcEnv

(* -------------------------------------------------------------------- *)
type ovkind =
| OVK_Type
| OVK_Operator

type clone_error =
| CE_DupOverride    of ovkind * symbol
| CE_UnkOverride    of ovkind * symbol
| CE_CrtOverride    of ovkind * symbol
| CE_TypeArgMism    of ovkind * symbol
| CE_OpIncompatible of symbol

exception CloneError of EcEnv.env * clone_error

val clone_error : EcEnv.env -> clone_error -> 'a

(* -------------------------------------------------------------------- *)
val clone : EcEnv.env -> theory_cloning -> symbol * ctheory_w3
