(* -------------------------------------------------------------------- *)
open EcSymbols
open EcPath

(* -------------------------------------------------------------------- *)
type memory = EcIdent.t

val mem_equal : memory -> memory -> bool

(* -------------------------------------------------------------------- *)
type local_memtype
type memtype = local_memtype option

val lmt_equal    : local_memtype -> local_memtype -> bool
val lmt_xpath    : local_memtype -> EcPath.xpath
val lmt_bindings : local_memtype -> EcTypes.ty Msym.t

val mt_equal    : memtype -> memtype -> bool
val mt_xpath    : memtype -> EcPath.xpath
val mt_bindings : memtype -> EcTypes.ty Msym.t

(* -------------------------------------------------------------------- *)
type memenv = memory * memtype

val me_equal : memenv -> memenv -> bool

(* -------------------------------------------------------------------- *)
exception DuplicatedMemoryBinding of symbol

val memory   : memenv -> memory
val memtype  : memenv -> memtype 
val xpath    : memenv -> EcPath.xpath
val bindings : memenv -> EcTypes.ty Msym.t

(* -------------------------------------------------------------------- *)
val empty_local : memory -> EcPath.xpath -> memenv
val abstract    : memory -> memenv

val bind   : symbol -> EcTypes.ty -> memenv -> memenv
val lookup : symbol -> memenv -> EcTypes.ty option
val is_bound : symbol -> memenv -> bool

(* -------------------------------------------------------------------- *)
val mt_subst :
  (EcPath.xpath -> EcPath.xpath) ->
  (EcTypes.ty -> EcTypes.ty) -> memtype -> memtype

val mt_substm :
  (EcPath.path -> EcPath.path) ->
  EcPath.mpath EcIdent.Mid.t ->
  (EcTypes.ty -> EcTypes.ty) -> memtype -> memtype

val me_subst :
  (EcPath.xpath -> EcPath.xpath) ->
  memory EcIdent.Mid.t ->
  (EcTypes.ty -> EcTypes.ty) -> memenv -> memenv

val me_substm :
 (EcPath.path -> EcPath.path) ->
  EcPath.mpath EcIdent.Mid.t ->
  memory EcIdent.Mid.t ->
  (EcTypes.ty -> EcTypes.ty) -> memenv -> memenv
