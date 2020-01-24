(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcSymbols

(* -------------------------------------------------------------------- *)
type memory = EcIdent.t

val mem_equal : memory -> memory -> bool

(* -------------------------------------------------------------------- *)
type proj_arg =
  { arg_ty : EcTypes.ty; (* type of the procedure argument "arg" *)
    arg_pos : int;       (* projection *)
    arg_len : int;       (* number of arguments *)
  }

type local_memtype

type memtype = local_memtype option

val lmt_equal    : local_memtype -> local_memtype -> bool
val lmt_bindings :
  local_memtype ->
  (proj_arg option * EcTypes.ty * EcIdent.t) Msym.t

val mt_equal    : memtype -> memtype -> bool
val mt_bindings : memtype -> (proj_arg option * EcTypes.ty * EcIdent.t) Msym.t
val mt_fv       : memtype -> int EcIdent.Mid.t

(* -------------------------------------------------------------------- *)
type memenv = memory * memtype

val me_equal : memenv -> memenv -> bool

(* -------------------------------------------------------------------- *)
exception DuplicatedMemoryBinding of symbol

val memory   : memenv -> memory
val memtype  : memenv -> memtype
val bindings : memenv -> (proj_arg option * EcTypes.ty * EcIdent.t) Msym.t

(* -------------------------------------------------------------------- *)
val empty_local : memory -> memenv
val abstract    : memory -> memenv

val bindp :
  proj_arg option -> EcTypes.ty -> EcIdent.t -> memenv -> memenv

val bind_proj :
  EcTypes.ty -> int -> int ->
  EcTypes.ty -> EcIdent.t -> memenv -> memenv

val bindp_new     : symbol -> proj_arg option -> EcTypes.ty -> memenv -> memenv * EcIdent.t
val bind_new      : symbol -> EcTypes.ty -> memenv -> memenv * EcIdent.t
val bind_proj_new : EcTypes.ty -> int -> int -> symbol -> EcTypes.ty -> memenv -> memenv * EcIdent.t

val lookup   :
  symbol -> memenv ->
  (proj_arg option * EcTypes.ty * EcIdent.t ) option
val is_bound : symbol -> memenv -> bool
val is_bound_pv : EcTypes.prog_var -> memenv -> bool

(* -------------------------------------------------------------------- *)
val mt_subst :
     (EcTypes.ty -> EcTypes.ty)
  -> memtype -> memtype

val mt_substm :
     (EcTypes.ty -> EcTypes.ty)
  -> memtype -> memtype

val me_subst :
     memory EcIdent.Mid.t
  -> (EcTypes.ty -> EcTypes.ty)
  -> memenv -> memenv

val me_substm :
     memory EcIdent.Mid.t
  -> (EcTypes.ty -> EcTypes.ty)
  -> memenv -> memenv
