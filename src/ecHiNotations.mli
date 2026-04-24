(* -------------------------------------------------------------------- *)
open EcSymbols
open EcParsetree
open EcLocation
open EcDecl
open EcEnv

(* -------------------------------------------------------------------- *)
type nterror =
| NTE_Typing        of EcTyping.tyerror
| NTE_TyNotClosed
| NTE_DupIdent
| NTE_UnknownBinder of symbol
| NTE_AbbrevIsVar
| NTE_UnknownSlot    of symbol
| NTE_DuplicateSlot  of symbol
| NTE_TemplateEmpty
| NTE_BadPunct       of string
| NTE_OptionalEmpty
| NTE_OptionalMustStartWithPunct
| NTE_DefaultOnNonOptional of symbol
| NTE_MissingDefault       of symbol

exception NotationError of EcLocation.t * EcEnv.env * nterror

val nterror : EcLocation.t -> env -> nterror -> 'a

(* -------------------------------------------------------------------- *)
val trans_notation : env -> pnotation located -> symbol * operator
val trans_abbrev   : env -> pabbrev   located -> symbol * operator
