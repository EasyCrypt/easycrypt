(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2014 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcPath
open EcTypes
open EcModules
open EcMemory

(* -------------------------------------------------------------------- *)
include module type of struct include EcCoreFol end

(* -------------------------------------------------------------------- *)
val f_losslessF: xpath -> form

val f_eqparams:
     xpath -> EcTypes.ty -> variable list option -> memory
  -> xpath -> EcTypes.ty -> variable list option -> memory
  -> form

val f_eqres:
     xpath -> EcTypes.ty -> memory
  -> xpath -> EcTypes.ty -> memory
  -> form

val f_eqglob:
     mpath -> memory
  -> mpath -> memory
  -> form

(* soft-constructors - ordering *)
val f_int_le  : form -> form -> form
val f_int_lt  : form -> form -> form
val f_int_sub : form -> form -> form

(* soft-constructors - reals *)
val f_rint : int -> form
val f_real_of_int : form -> form

val f_r0 : form
val f_r1 : form

(* soft-constructor - numbers *)
val f_int_intval : form -> form -> form
val f_int_sum    : form -> form -> EcTypes.ty -> form

val f_real_le : form -> form -> form
val f_real_lt : form -> form -> form

val f_real_div : form -> form -> form
val f_real_add : form -> form -> form
val f_real_sub : form -> form -> form
val f_real_mul : form -> form -> form

(* soft constructors - distributions *)
val fop_in_supp : EcTypes.ty -> form
val fop_mu_x    : EcTypes.ty -> form

val f_in_supp : form -> form -> form
val f_mu      : form -> form -> form
val f_mu_x    : form -> form -> form
val f_weight  : EcTypes.ty -> form -> form

(* common functions *)
val f_identity : ?name:EcSymbols.symbol -> EcTypes.ty -> form

(* -------------------------------------------------------------------- *)
(* WARNING : this function should be use only in a context ensuring
 * that the quantified variables can be instanciated *)

val f_proj_simpl : form -> int -> EcTypes.ty -> form
val f_if_simpl   : form -> form -> form -> form
val f_let_simpl  : EcTypes.lpattern -> form -> form -> form
val f_lets_simpl : (EcTypes.lpattern * form) list -> form -> form

val f_forall_simpl  : binding -> form -> form
val f_exists_simpl  : binding -> form -> form
val f_quant_simpl   : quantif -> binding -> form -> form
val f_app_simpl     : form -> form list -> EcTypes.ty -> form
val f_betared_simpl : binding -> form -> form list -> EcTypes.ty -> form

val f_not_simpl  : form -> form
val f_and_simpl  : form -> form -> form
val f_ands_simpl : form list -> form -> form
val f_anda_simpl : form -> form -> form
val f_or_simpl   : form -> form -> form
val f_ora_simpl  : form -> form -> form
val f_imp_simpl  : form -> form -> form
val f_imps       : form list -> form -> form
val f_imps_simpl : form list -> form -> form
val f_iff_simpl  : form -> form -> form
val f_eq_simpl   : form -> form -> form

val f_int_le_simpl  : form -> form -> form
val f_int_lt_simpl  : form -> form -> form
val f_real_le_simpl : form -> form -> form
val f_real_lt_simpl : form -> form -> form

val f_int_add_simpl : form -> form -> form
val f_int_sub_simpl : form -> form -> form
val f_int_mul_simpl : form -> form -> form

val f_real_add_simpl : form -> form -> form
val f_real_sub_simpl : form -> form -> form
val f_real_mul_simpl : form -> form -> form
val f_real_div_simpl : form -> form -> form

(* -------------------------------------------------------------------- *)
val destr_exists_prenex : form -> binding * form

(* -------------------------------------------------------------------- *)
type op_kind =
  | OK_true
  | OK_false
  | OK_not
  | OK_and   of bool  (* true = asym *)
  | OK_or    of bool  (* true = asym *)
  | OK_imp
  | OK_iff
  | OK_eq
  | OK_int_le
  | OK_int_lt
  | OK_real_le
  | OK_real_lt
  | OK_int_add
  | OK_int_sub
  | OK_int_mul
  | OK_int_exp
  | OK_int_opp
  | OK_real_add
  | OK_real_sub
  | OK_real_mul
  | OK_real_div
  | OK_other

val op_kind       : path -> op_kind
val is_logical_op : path -> bool

(* -------------------------------------------------------------------- *)
(* Structured formulas - allows to get more information on the top-level
 * structure of a formula via direct pattern matching *)

type sform =
  | SFint   of int
  | SFlocal of EcIdent.t
  | SFpvar  of EcTypes.prog_var * memory
  | SFglob  of mpath * memory

  | SFif    of form * form * form
  | SFlet   of lpattern * form * form
  | SFtuple of form list
  | SFproj  of form * int

  | SFquant of quantif * (EcIdent.t * gty) * form Lazy.t
  | SFtrue
  | SFfalse
  | SFnot   of form
  | SFand   of bool * (form * form)
  | SFor    of bool * (form * form)
  | SFimp   of form * form
  | SFiff   of form * form
  | SFeq    of form * form
  | SFop    of (path * ty list) * (form list)

  | SFhoareF   of hoareF
  | SFhoareS   of hoareS
  | SFbdHoareF of bdHoareF
  | SFbdHoareS of bdHoareS
  | SFequivF   of equivF
  | SFequivS   of equivS
  | SFpr       of pr

  | SFother of form

val sform_of_form : form -> sform
