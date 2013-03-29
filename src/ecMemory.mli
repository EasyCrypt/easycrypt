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
val mpath    : memenv -> EcPath.mpath
val bindings : memenv -> EcTypes.ty Msym.t

(* -------------------------------------------------------------------- *)
val empty  : memory -> EcPath.mpath -> memenv
val bind   : symbol -> EcTypes.ty -> memenv -> memenv

val lookup : symbol -> memenv -> EcTypes.ty option

(* -------------------------------------------------------------------- *)

val me_subst :
  (EcPath.path -> EcPath.path) ->
  EcPath.mpath EcIdent.Mid.t ->
  memory EcIdent.Mid.t ->
  (EcTypes.ty -> EcTypes.ty) -> memenv -> memenv



