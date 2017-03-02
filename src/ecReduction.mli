(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcIdent
open EcPath
open EcTypes
open EcFol
open EcModules
open EcEnv

(* -------------------------------------------------------------------- *)
exception IncompatibleType of env * (ty * ty)
exception IncompatibleForm of env * (form * form)

(* -------------------------------------------------------------------- *)
type 'a eqtest = env -> 'a -> 'a -> bool
type 'a eqntest = env -> ?norm:bool -> 'a -> 'a -> bool

module EqTest : sig
  val for_type_exn : env -> ty -> ty -> unit

  val for_type  : ty       eqtest
  val for_pv    : prog_var eqntest
  val for_xp    : xpath    eqntest
  val for_mp    : mpath    eqntest
  val for_instr : instr    eqntest
  val for_stmt  : stmt     eqntest
  val for_expr  : expr     eqntest

  val is_unit : env -> ty -> bool
  val is_bool : env -> ty -> bool
  val is_int  : env -> ty -> bool
end

val is_alpha_eq : LDecl.hyps -> form -> form -> bool

(* -------------------------------------------------------------------- *)
type reduction_info = {
  beta    : bool;
  delta_p : (path  -> bool); (* None means all *)
  delta_h : (ident -> bool); (* None means all *)
  zeta    : bool;            (* reduce let  *)
  iota    : bool;            (* reduce case *)
  eta     : bool;            (* reduce eta-expansion *)
  logic   : rlogic_info;     (* perform logical simplification *)
  modpath : bool;            (* reduce module path *)
}

and rlogic_info = [`Full | `ProductCompat] option

val full_red     : reduction_info
val no_red       : reduction_info
val beta_red     : reduction_info
val betaiota_red : reduction_info
val nodelta      : reduction_info

val h_red_opt : reduction_info -> LDecl.hyps -> form -> form option
val h_red     : reduction_info -> LDecl.hyps -> form -> form

val simplify : reduction_info -> LDecl.hyps -> form -> form

val is_conv    : LDecl.hyps -> form -> form -> bool
val check_conv : LDecl.hyps -> form -> form -> unit

(* -------------------------------------------------------------------- *)
type xconv = [`Eq | `AlphaEq | `Conv]

val xconv : xconv -> LDecl.hyps -> form -> form -> bool
