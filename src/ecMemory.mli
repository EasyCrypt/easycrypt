(* -------------------------------------------------------------------- *)
open EcSymbols
open EcPath

(* -------------------------------------------------------------------- *)
type memory = EcIdent.t

val mem_equal : memory -> memory -> bool

(* -------------------------------------------------------------------- *)
type memenv

val me_equal : memenv -> memenv -> bool

(* -------------------------------------------------------------------- *)
exception DuplicatedMemoryBinding of symbol

val memory   : memenv -> memory
val bindings : memenv -> EcTypes.ty Msym.t

(* -------------------------------------------------------------------- *)
val empty  : memory -> memenv
val bind   : symbol -> EcTypes.ty -> memenv -> memenv

val lookup : symbol -> memenv -> EcTypes.ty option

(* until a constructor is defined *)
val dummy_memenv : memenv
