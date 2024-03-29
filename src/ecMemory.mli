(* -------------------------------------------------------------------- *)
open EcSymbols
open EcTypes
(* -------------------------------------------------------------------- *)
type memory = EcAst.memory

val mem_equal : memory -> memory -> bool

(* -------------------------------------------------------------------- *)
type proj_arg = EcAst.proj_arg

type memtype = EcAst.memtype

val mt_equal_gen : (ty -> ty -> bool) -> memtype -> memtype -> bool
val mt_equal    : memtype -> memtype -> bool
val mt_fv       : memtype -> int EcIdent.Mid.t

val mt_iter_ty : (ty -> unit) -> memtype -> unit

(* -------------------------------------------------------------------- *)
type memenv = EcAst.memenv

val me_equal_gen : (ty -> ty -> bool) -> memenv -> memenv -> bool
val me_equal : memenv -> memenv -> bool

(* -------------------------------------------------------------------- *)
val memory   : memenv -> memory
val memtype  : memenv -> memtype

(* -------------------------------------------------------------------- *)
(* [empty_local witharg id] if witharg then allows to use symbol "arg"  *)
val empty_local    : witharg:bool -> memory -> memenv
val empty_local_mt : witharg:bool -> memtype

val abstract    : memory -> memenv
val abstract_mt : memtype

exception DuplicatedMemoryBinding of symbol

val bindall    : ovariable list -> memenv -> memenv
val bindall_mt : ovariable list -> memtype -> memtype

val bind_fresh : ovariable -> memenv -> memenv * ovariable
val bindall_fresh : ovariable list -> memenv -> memenv * ovariable list

(* -------------------------------------------------------------------- *)
val lookup :
  symbol -> memtype -> (variable * proj_arg option * int option) option

val lookup_me :
  symbol -> memenv -> (variable * proj_arg option * int option) option

val get_name :
  symbol -> int option -> memenv -> symbol option

val is_bound : symbol -> memtype -> bool
val is_bound_pv : EcTypes.prog_var -> memtype -> bool

(* -------------------------------------------------------------------- *)
val mt_subst : (ty -> ty) -> memtype -> memtype

val me_subst : memory EcIdent.Mid.t -> (ty -> ty) -> memenv -> memenv

(* -------------------------------------------------------------------- *)
val for_printing : memtype -> (symbol option * ovariable list) option

val dump_memtype : memtype -> string

(* -------------------------------------------------------------------- *)
val local_type : memtype -> ty option
val has_locals : memtype -> bool
