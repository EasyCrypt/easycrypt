(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcBigInt
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
val f_rint : zint -> form
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
val f_mu      : EcEnv.env -> form -> form -> form
val f_mu_x    : form -> form -> form
val f_weight  : EcTypes.ty -> form -> form

(* common functions *)
val f_identity : ?name:EcSymbols.symbol -> EcTypes.ty -> form

(* -------------------------------------------------------------------- *)
(* WARNING : this function should be use only in a context ensuring
 * that the quantified variables can be instanciated *)

val f_betared : form -> form

val f_proj_simpl : form -> int -> EcTypes.ty -> form
val f_if_simpl   : form -> form -> form -> form
val f_let_simpl  : EcTypes.lpattern -> form -> form -> form
val f_lets_simpl : (EcTypes.lpattern * form) list -> form -> form

val f_forall_simpl : bindings -> form -> form
val f_exists_simpl : bindings -> form -> form
val f_quant_simpl  : quantif -> bindings -> form -> form
val f_app_simpl    : form -> form list -> EcTypes.ty -> form

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
val destr_exists_prenex : form -> bindings * form

(* -------------------------------------------------------------------- *)
(* projects 'a Distr type into 'a *)
val proj_distr_ty : EcEnv.env -> ty -> ty

(* -------------------------------------------------------------------- *)
type op_kind = [
  | `True
  | `False
  | `Not
  | `And   of [`Asym | `Sym]
  | `Or    of [`Asym | `Sym]
  | `Imp
  | `Iff
  | `Eq
  | `Int_le
  | `Int_lt
  | `Real_le
  | `Real_lt
  | `Int_add
  | `Int_sub
  | `Int_mul
  | `Int_pow
  | `Int_opp
  | `Real_add
  | `Real_sub
  | `Real_mul
  | `Real_div
]

val op_kind       : path -> op_kind option
val is_logical_op : path -> bool

(* -------------------------------------------------------------------- *)
(* Structured formulas - allows to get more information on the top-level
 * structure of a formula via direct pattern matching *)

type sform =
  | SFint   of zint
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
  | SFand   of [`Asym | `Sym] * (form * form)
  | SFor    of [`Asym | `Sym] * (form * form)
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
