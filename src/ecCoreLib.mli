(* -------------------------------------------------------------------- *)
open EcSymbols
open EcPath

(* -------------------------------------------------------------------- *)
(* Symbols with dedicated parsing rules                                 *)

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
val i_top  : symbol
val i_self : symbol
val p_top  : path

(* -------------------------------------------------------------------- *)
val i_Pervasive : symbol
val p_Pervasive : path

(* -------------------------------------------------------------------- *)
val base_rnd : string
val base_ll  : string

(* -------------------------------------------------------------------- *)
module CI_Unit : sig
  val p_unit : path
  val p_tt   : path
end
(*-------------------------------------------------------------------- *)
module CI_Witness : sig
  val p_witness : path
end

(* -------------------------------------------------------------------- *)
module CI_Option : sig
  val p_option : path
  val p_none   : path
  val p_some   : path
  val p_oget   : path
end

(*-------------------------------------------------------------------- *)
module CI_Bool : sig
  val i_Bool : symbol
  val p_Bool : path
  val p_bool : path

  val p_true  : path
  val p_false : path

  val p_not  : path
  val p_anda : path
  val p_and  : path
  val p_ora  : path
  val p_or   : path
  val p_imp  : path
  val p_iff  : path
  val p_eq   : path
end

(* -------------------------------------------------------------------- *)
module CI_Int : sig
  val i_Int : symbol
  val p_Int : path
  val p_int : path

  val p_int_elim : path

  val p_int_opp   : path
  val p_int_add   : path
  val p_int_mul   : path
  val p_int_le    : path
  val p_int_lt    : path
  val p_int_pow   : path
  val p_int_edivz : path
  val p_iteri     : path
end

(* -------------------------------------------------------------------- *)
module CI_xint : sig
  val p_Xint      : path
  val p_xint      : path
  val p_N         : path
  val p_inf       : path
  val p_xopp      : path
  val p_xadd      : path
  val p_xmul      : path
  val p_is_int    : path
  val p_is_inf    : path
end

(* -------------------------------------------------------------------- *)
module CI_Real : sig
  val i_Real : symbol
  val p_Real : path
  val p_real : path

  val p_RealExtra : path
  val p_RealOrder : path

  val p_real0       : path
  val p_real1       : path
  val p_real_opp    : path
  val p_real_add    : path
  val p_real_mul    : path
  val p_real_inv    : path
  val p_real_pow    : path
  val p_real_le     : path
  val p_real_lt     : path
  val p_real_of_int : path
  val p_real_abs    : path

  val real_lemma    : string -> path
  val real_order_lemma : string -> path

end

(* -------------------------------------------------------------------- *)
module CI_Xreal : sig
  val p_Xreal        : path

  val p_realp        : path
  val p_of_real      : path

  val p_xreal        : path
  val p_rp           : path
  val p_inf          : path
  val p_xadd         : path
  val p_xmul         : path
  val p_xle          : path
  val p_is_real      : path
  val p_is_inf       : path
  val p_interp_form  : path
  val p_Ep           : path
  val p_concave_incr : path

  val p_xle_cxr_l : path
  val p_xle_cxr_r : path

end

(* -------------------------------------------------------------------- *)
module CI_Pred : sig
  val i_Pred : symbol
  val p_Pred : path

  val p_predT      : path
  val p_pred1      : path
end

(* -------------------------------------------------------------------- *)
module CI_Distr : sig
  val i_Distr : symbol
  val p_Distr : path
  val p_distr : path

  val p_dbool      : path
  val p_dbitstring : path
  val p_dinter     : path
  val p_dunit      : path
  val p_dlet       : path
  val p_dmap       : path

  val p_support : path
  val p_mu      : path
  val p_lossless: path
  val p_uniform : path
  val p_full    : path
  val p_dfold   : path
end

(* -------------------------------------------------------------------- *)
module CI_Sum : sig
  val i_Sum : symbol
  val p_Sum : path

  val p_sum : path
end

(* -------------------------------------------------------------------- *)
module CI_Map : sig
  val i_Map  : symbol
  val p_Map  : path
  val p_map  : path
  val p_get  : path
  val p_set  : path
  val p_cst  : path
end

(* -------------------------------------------------------------------- *)
module CI_Logic : sig

  val i_Logic  : symbol
  val p_Logic  : path
  val mk_logic : symbol -> path

  val p_unit_elim     : path
  val p_false_elim    : path
  val p_bool_elim     : path
  val p_and_elim      : path
  val p_anda_elim     : path
  val p_and_proj_l    : path
  val p_and_proj_r    : path
  val p_anda_proj_l   : path
  val p_anda_proj_r   : path
  val p_anda_proj_rs  : path
  val p_or_elim       : path
  val p_ora_elim      : path
  val p_iff_elim      : path
  val p_if_elim       : path

  val p_true_intro    : path
  val p_and_intro     : path
  val p_anda_intro    : path
  val p_anda_intro_s  : path
  val p_or_intro_l    : path
  val p_ora_intro_l   : path
  val p_or_intro_r    : path
  val p_ora_intro_r   : path
  val p_iff_intro     : path
  val p_if_intro      : path
  val p_if_congr      : path
  val p_eq_refl       : path
  val p_eq_iff        : path
  val p_eq_trans      : path
  val p_eq_ind        : path
  val p_fcongr        : path
  val p_eq_sym        : path
  val p_eq_sym_imp    : path
  val p_eq_iff_imp    : path
  val p_negeqF        : path

  val p_iff_lr        : path
  val p_iff_rl        : path

  val p_cut_lemma     : path
  val p_case_eq_bool  : path
  val p_ip_dup        : path

  val p_negbTE        : path
end
