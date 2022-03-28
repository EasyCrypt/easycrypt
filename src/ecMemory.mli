(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2021 - Inria
 * Copyright (c) - 2012--2021 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcSymbols
open EcTypes
(* -------------------------------------------------------------------- *)
type memory = EcIdent.t

val mem_equal : memory -> memory -> bool

(* -------------------------------------------------------------------- *)
type proj_arg =
  { arg_ty  : ty; (* type of the procedure argument "arg" *)
    arg_pos : int;       (* projection *)
  }

type memtype

val mt_equal_gen : (ty -> ty -> bool) -> memtype -> memtype -> bool
val mt_equal    : memtype -> memtype -> bool
val mt_fv       : memtype -> int EcIdent.Mid.t

val mt_iter_ty : (ty -> unit) -> memtype -> unit

(* -------------------------------------------------------------------- *)
type memenv = memory * memtype

val mem_hash : memenv -> int
val me_equal_gen : (ty -> ty -> bool) -> memenv -> memenv -> bool
val me_equal : memenv -> memenv -> bool

(* -------------------------------------------------------------------- *)
val memory   : memenv -> memory
val memtype  : memenv -> memtype

(* -------------------------------------------------------------------- *)
(* [empty_local witharg id] if witharg then allows to use symbol "arg"  *)
val empty_local    : witharg:bool -> memory -> memenv
val empty_local_mt : witharg:bool -> memtype

val schema    : memory -> memenv
val schema_mt : memtype

val abstract    : memory -> memenv
val abstract_mt : memtype

val is_schema : memtype -> bool

exception DuplicatedMemoryBinding of symbol

val bindall    : variable list -> memenv -> memenv
val bindall_mt : variable list -> memtype -> memtype

val bind_fresh : variable -> memenv -> memenv * variable
val bindall_fresh : variable list -> memenv -> memenv * variable list

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
val for_printing : memtype -> (symbol option * variable list) option

val dump_memtype : memtype -> string

(* -------------------------------------------------------------------- *)
val local_type : memtype -> ty option
val has_locals : memtype -> bool
