(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
let s_get  = "_.[_]"
let s_set  = "_.[_<-_]"
let s_nil  = "[]"
let s_cons = "::"
let s_abs  = "`|_|"

(* -------------------------------------------------------------------- *)
let i_top  = "Top"
let i_self = "Self"
let p_top  = EcPath.psymbol i_top

(* -------------------------------------------------------------------- *)
let i_Pervasive = "Pervasive"
let p_Pervasive = EcPath.pqname p_top i_Pervasive
let _Pervasive  = fun x -> EcPath.pqname p_Pervasive x

(* -------------------------------------------------------------------- *)
let base_rnd = "random"
let base_ll  = "lossless"

(*-------------------------------------------------------------------- *)
module CI_Unit = struct
  let p_unit  = _Pervasive "unit"
  let p_tt    = _Pervasive "tt"
end

(*-------------------------------------------------------------------- *)
module CI_Bool = struct
  let i_Bool = "Bool"
  let p_Bool = EcPath.pqname p_top i_Bool
  let p_bool = _Pervasive "bool"

  let p_true  = _Pervasive "true"
  let p_false = _Pervasive "false"

  let p_not  = _Pervasive "[!]"
  let p_anda = _Pervasive "&&"
  let p_and  = _Pervasive "/\\"
  let p_ora  = _Pervasive "||"
  let p_or   = _Pervasive "\\/"
  let p_imp  = _Pervasive "=>"
  let p_iff  = _Pervasive "<=>"
  let p_eq   = _Pervasive "="
end

(* -------------------------------------------------------------------- *)
module CI_Int = struct
  let i_Int = "CoreInt"
  let p_Int = EcPath.pqname p_top i_Int
  let p_int = _Pervasive "int"

  let i_IntDiv = "IntDiv"
  let p_IntDiv = EcPath.pqname p_top i_IntDiv

  let _Int    = fun x -> EcPath.pqname p_Int x
  let _IntDiv = fun x -> EcPath.pqname p_IntDiv x

  let p_int_elim  = _Int "intind"
  let p_int_opp   = _Int "opp"
  let p_int_add   = _Int "add"
  let p_int_mul   = _Int "mul"
  let p_int_pow   = EcPath.extend p_top ["Ring"; "IntID"; "exp"]
  let p_int_le    = _Int "le"
  let p_int_lt    = _Int "lt"
  let p_int_edivz = _IntDiv "edivz"
end

(* -------------------------------------------------------------------- *)
module CI_Real = struct
  let i_Real = "CoreReal"
  let p_Real = EcPath.pqname p_top i_Real
  let p_real = _Pervasive "real"

  let p_RealExtra = EcPath.pqname p_top "Real"


  let p_RealOrder =
    EcPath.extend p_top ["StdOrder"; "RealOrder"]

  let _Real = fun x -> EcPath.pqname p_Real x

  let p_real0       = _Real "zero"
  let p_real1       = _Real "one"
  let p_real_opp    = _Real "opp"
  let p_real_add    = _Real "add"
  let p_real_mul    = _Real "mul"
  let p_real_inv    = _Real "inv"
  let p_real_pow    = EcPath.extend p_top ["Real"; "Rfield"; "exp"]
  let p_real_le     = _Real "le"
  let p_real_lt     = _Real "lt"
  let p_real_of_int = _Real "from_int"
  let p_real_abs    = EcPath.extend p_top ["Real"; "`|_|"]
end

module CI_Pred = struct
  let i_Pred  = "Logic"
  let p_Pred  = EcPath.pqname p_top i_Pred

  let _Pred x = EcPath.pqname p_Pred x
  let p_predT = _Pred "predT"
  let p_pred1 = _Pred "pred1"
end

(* -------------------------------------------------------------------- *)
module CI_Distr = struct
  let i_Distr = "Distr"
  let p_Distr = EcPath.pqname p_top i_Distr
  let p_distr = _Pervasive "distr"
  let _Distr  = fun x -> EcPath.pqname p_Distr x

  let p_dbool      = EcPath.extend p_top ["DBool"; "dbool"]
  let p_dbitstring = EcPath.extend p_Distr ["Dbitstring"; "dbitstring"]
  let p_dinter     = EcPath.extend p_top ["DInterval"; "dinter"]

  let p_support  = _Distr "support"
  let p_mu       = _Pervasive "mu"
  let p_lossless = _Distr "is_lossless"
  let p_uniform  = _Distr "is_uniform"
  let p_full     = _Distr "is_full"
end

(* -------------------------------------------------------------------- *)
module CI_Map = struct
  let i_Map = "CoreMap"
  let p_Map = EcPath.pqname p_top i_Map
  let _Map  = fun x -> EcPath.pqname p_Map x

  let p_map = _Map "map"
  let p_get = _Map s_get
  let p_set = _Map s_set
  let p_cst = _Map "cst"
end

(* -------------------------------------------------------------------- *)
module CI_Logic = struct
  let i_Logic  = "Tactics"
  let p_Logic  = EcPath.pqname p_top i_Logic
  let _Logic   = fun x -> EcPath.pqname p_Logic x
  let mk_logic = _Logic

  let p_unit_elim     = _Logic "unitW"
  let p_false_elim    = _Logic "falseW"
  let p_bool_elim     = _Logic "boolW"
  let p_and_elim      = _Logic "andW"
  let p_anda_elim     = _Logic "andaW"
  let p_and_proj_l    = _Logic "andWl"
  let p_and_proj_r    = _Logic "andWr"
  let p_anda_proj_l   = _Logic "andaWl"
  let p_anda_proj_r   = _Logic "andaWr"
  let p_or_elim       = _Logic "orW"
  let p_ora_elim      = _Logic "oraW"
  let p_iff_elim      = _Logic "iffW"
  let p_if_elim       = _Logic "ifW"

  let p_true_intro    = _Logic "trueI"
  let p_and_intro     = _Logic "andI"
  let p_anda_intro    = _Logic "andaI"
  let p_or_intro_l    = _Logic "orIl"
  let p_ora_intro_l   = _Logic "oraIl"
  let p_or_intro_r    = _Logic "orIr"
  let p_ora_intro_r   = _Logic "oraIr"
  let p_iff_intro     = _Logic "iffI"
  let p_if_intro      = _Logic "ifI"
  let p_if_congr      = _Logic "if_congr"
  let p_eq_refl       = _Logic "eq_refl"
  let p_eq_trans      = _Logic "eq_trans"
  let p_eq_iff        = _Logic "eq_iff"
  let p_fcongr        = _Logic "congr1"
  let p_eq_ind        = _Logic "eq_ind"
  let p_eq_sym        = _Logic "eq_sym"
  let p_eq_sym_imp    = _Logic "eq_sym_imp"
  let p_negbTE        = _Logic "negbTE"
  let p_negeqF        = _Logic "negeqF"

  let p_iff_lr        = _Logic "iffLR"
  let p_iff_rl        = _Logic "iffRL"

  let p_cut_lemma     = _Logic "cut_"
  let p_case_eq_bool  = _Logic "boolWE"
  let p_ip_dup        = _Logic "dup"
end

(* -------------------------------------------------------------------- *)
let is_mixfix_op =
  let ops = [s_get; s_set; s_nil; s_abs] in
  fun op -> List.mem op ops

(* -------------------------------------------------------------------- *)
let s_real_of_int = EcPath.toqsymbol CI_Real.p_real_of_int
let s_dbool       = EcPath.toqsymbol CI_Distr.p_dbool
let s_dbitstring  = EcPath.toqsymbol CI_Distr.p_dbitstring
let s_dinter      = EcPath.toqsymbol CI_Distr.p_dinter
