(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
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

  val for_type  : ty          eqtest
  val for_pv    : prog_var    eqntest
  val for_xp    : xpath       eqntest
  val for_mp    : mpath       eqntest
  val for_instr : instr       eqntest
  val for_stmt  : stmt        eqntest
  val for_expr  : expr        eqntest
  val for_msig  : module_sig  eqntest
  val for_mexpr : module_expr eqntest

  val is_unit : env -> ty -> bool
  val is_bool : env -> ty -> bool
  val is_int  : env -> ty -> bool
end

val is_alpha_eq : LDecl.hyps -> form -> form -> bool

(* -------------------------------------------------------------------- *)
module User : sig
  type options = EcTheory.rule_option

  type error =
    | MissingVarInLhs   of EcIdent.t
    | MissingTyVarInLhs of EcIdent.t
    | NotAnEq
    | NotFirstOrder
    | RuleDependsOnMemOrModule
    | HeadedByVar

  exception InvalidUserRule of error

  type rule = EcEnv.Reduction.rule

  val compile : opts:options -> prio:int -> EcEnv.env -> EcPath.path -> rule
end

(* -------------------------------------------------------------------- *)
val can_eta : ident -> form * form list -> bool

(* -------------------------------------------------------------------- *)
type reduction_info = {
  beta    : bool;
  delta_p : (path  -> deltap); (* reduce operators *)
  delta_h : (ident -> bool);   (* reduce local definitions *)
  zeta    : bool;              (* reduce let  *)
  iota    : bool;              (* reduce case *)
  eta     : bool;              (* reduce eta-expansion *)
  logic   : rlogic_info;       (* perform logical simplification *)
  modpath : bool;              (* reduce module path *)
  user    : bool               (* reduce user defined rules *)
}

and deltap      = [`Yes | `No | `Force]
and rlogic_info = [`Full | `ProductCompat] option

val full_red     : reduction_info
val full_compat  : reduction_info
val no_red       : reduction_info
val beta_red     : reduction_info
val betaiota_red : reduction_info
val nodelta      : reduction_info
val delta        : reduction_info

val h_red_opt : reduction_info -> LDecl.hyps -> form -> form option
val h_red     : reduction_info -> LDecl.hyps -> form -> form

val reduce_user_gen :
  (EcFol.form -> EcFol.form) ->
  reduction_info ->
  EcEnv.env -> EcEnv.LDecl.hyps -> EcFol.form -> EcFol.form

val simplify : reduction_info -> LDecl.hyps -> form -> form

val is_conv    : ?ri:reduction_info -> LDecl.hyps -> form -> form -> bool
val check_conv : ?ri:reduction_info -> LDecl.hyps -> form -> form -> unit

val check_bindings :
  exn -> EcEnv.env -> EcFol.f_subst ->
  (EcIdent.t * EcFol.gty) list -> (EcIdent.t * EcFol.gty) list ->
  EcEnv.env * EcFol.f_subst
(* -------------------------------------------------------------------- *)
type xconv = [`Eq | `AlphaEq | `Conv]

val xconv : xconv -> LDecl.hyps -> form -> form -> bool

(* -------------------------------------------------------------------- *)
