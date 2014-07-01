(* Copyright (c) - 2012-2014 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-B license *)

(* ----------------------------------------------------------------------*)
open EcSymbols
open EcPath

(* -------------------------------------------------------------------- *)
(*               Symbols with dedicated parsing rules                   *)
(* -------------------------------------------------------------------- *)
val s_get  : symbol
val s_set  : symbol
val s_nil  : symbol
val s_cons : symbol
val s_abs  : symbol

val is_mixfix_op : symbol -> bool

val s_dbool       : qsymbol
val s_dbitstring  : qsymbol
val s_dinter      : qsymbol
val s_real_of_int : qsymbol

(* -------------------------------------------------------------------- *)
(*                         Top-level theory                             *)
(* -------------------------------------------------------------------- *)
val id_top : symbol
val p_top  : path

val id_Pervasive : symbol
val p_Pervasive  : path

val id_Logic : symbol
val p_Logic  : path
val mk_logic : symbol -> path

(* -------------------------------------------------------------------- *)
(*                            Core Types                                *)
(* -------------------------------------------------------------------- *)
val p_unit  : path
val p_bool  : path
val p_int   : path
val p_real  : path
val p_distr : path 
val p_fset  : path

(* -------------------------------------------------------------------- *)
(*                  Core constructors / operators                       *)
(* -------------------------------------------------------------------- *)
val p_tt    : path
val p_true  : path
val p_false : path

(* -------------------------------------------------------------------- *)
(*                        Logical operators                             *)
(* -------------------------------------------------------------------- *)
val p_not  : path
val p_and  : path
val p_anda : path
val p_or   : path
val p_ora  : path
val p_imp  : path
val p_iff  : path
val p_eq   : path

(* -------------------------------------------------------------------- *)
(*                      Operations on integers                          *)
(* -------------------------------------------------------------------- *)
val p_int_add : path
val p_int_opp : path
val p_int_sub : path
val p_int_mul : path
val p_int_pow : path

val p_real_of_int : path

val p_int_le : path
val p_int_lt : path

(* -------------------------------------------------------------------- *)
(*                       Operations on reals                            *)
(* -------------------------------------------------------------------- *)
val p_real_add : path
val p_real_opp : path
val p_real_sub : path
val p_real_mul : path
val p_real_div : path
val p_real_pow : path

val p_real_of_int : path

val p_real_le : path
val p_real_lt : path
val p_real_ge : path

val p_rle_ge_sym  : path
(* -------------------------------------------------------------------- *)
(*                            Intervals                                 *)
(* -------------------------------------------------------------------- *)
val p_Sum        : path
val p_int_intval : path
val p_int_sum    : path

(* -------------------------------------------------------------------- *)
(*                          Distributions                               *)
(* -------------------------------------------------------------------- *)
val p_in_supp : path
val p_mu      : path
val p_mu_x    : path
val p_weight  : path

(* -------------------------------------------------------------------- *)
(*                          Logical lemmas                              *)
(* -------------------------------------------------------------------- *)
val p_cut_lemma  : path
val p_unit_elim  : path
val p_false_elim : path
val p_and_elim   : path
val p_and_proj_l : path
val p_and_proj_r : path
val p_anda_elim  : path
val p_or_elim    : path
val p_ora_elim   : path
val p_iff_elim   : path 
val p_if_elim    : path 

val p_true_intro  : path 
val p_and_intro   : path 
val p_anda_intro  : path 
val p_or_intro_l  : path 
val p_ora_intro_l : path 
val p_or_intro_r  : path 
val p_ora_intro_r : path 
val p_iff_intro   : path 
val p_if_intro    : path 
val p_eq_refl     : path
val p_eq_trans    : path
val p_eq_sym      : path
val p_eq_sym_imp  : path
val p_fcongr      : path
val p_imp_trans   : path

val p_rewrite_l     : path 
val p_rewrite_r     : path 
val p_rewrite_iff_l : path 
val p_rewrite_iff_r : path 
val p_rewrite_bool  : path

val p_case_eq_bool  : path 
val p_tuple_ind     : int -> path

val p_iff_lr : path
val p_iff_rl : path

val p_negbTE : path
