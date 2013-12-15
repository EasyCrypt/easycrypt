(* -------------------------------------------------------------------- *)
let s_get  = "_.[_]"
let s_set  = "_.[_<-_]"
let s_nil  = "[]"
let s_cons = "_::_"
let s_abs  = "`|_|"

(* -------------------------------------------------------------------- *)
let mixfix_ops = [s_get; s_set; s_nil; s_cons; s_abs]

let is_mixfix_op op =
  List.mem op mixfix_ops

(* -------------------------------------------------------------------- *)
(*                         Top-level theory                             *)
(* -------------------------------------------------------------------- *)
let id_top = "Top"
let p_top  = EcPath.psymbol id_top

(* -------------------------------------------------------------------- *)
(*                            Core Types                                *)
(* -------------------------------------------------------------------- *)
let id_Pervasive  = "Pervasive"
let p_Pervasive   = EcPath.pqname p_top id_Pervasive
let _Pervasive    = fun x -> EcPath.pqname p_Pervasive x

let p_unit  = _Pervasive "unit"
let p_bool  = _Pervasive "bool"
let p_int   = _Pervasive "int"
let p_real  = _Pervasive "real"
let p_distr = _Pervasive "distr"

(* -------------------------------------------------------------------- *)
(*                         Numbers theories                             *)
(* -------------------------------------------------------------------- *)
let id_Int  = "Int"
let id_Real = "Real"

let p_Int  = EcPath.pqname p_top id_Int 
let p_Real = EcPath.pqname p_top id_Real

(* --------------------------------------------------------------------- *)
(*                    Symbols for alg. operators                         *)
(* --------------------------------------------------------------------  *)
let id_add = "+"
let id_sub = "-"
let id_opp = "[-]"
let id_mul = "*"
let id_div = "/"
let id_pow = "^"

let id_le  = "<="
let id_lt  = "<"
let id_ge  = ">="

(* -------------------------------------------------------------------- *)
(*                  Core constructors / operators                       *)
(* -------------------------------------------------------------------- *)
let p_tt    = _Pervasive "tt"
let p_true  = _Pervasive "true"
let p_false = _Pervasive "false"

(* -------------------------------------------------------------------- *)
(*                        Logical operators                             *)
(* -------------------------------------------------------------------- *)
let p_not  = _Pervasive "[!]"
let p_anda = _Pervasive "&&"
let p_and  = _Pervasive "/\\"
let p_ora  = _Pervasive "||"
let p_or   = _Pervasive "\\/"
let p_imp  = _Pervasive "=>"
let p_iff  = _Pervasive "<=>"
let p_eq   = _Pervasive "="

(* -------------------------------------------------------------------- *)
(*                      Operations on integers                          *)
(* -------------------------------------------------------------------- *)
let _Int = fun x -> EcPath.pqname p_Int x

let p_int_opp = _Int id_opp
let p_int_add = _Int id_add
let p_int_sub = _Int id_sub
let p_int_mul = _Int id_mul
let p_int_pow = _Int id_pow   
let p_int_le  = _Int id_le
let p_int_lt  = _Int id_lt

let p_real_of_int = List.fold_left EcPath.pqname p_Real ["FromInt"; "from_int"]
let s_real_of_int = EcPath.toqsymbol p_real_of_int

(* -------------------------------------------------------------------- *)
(*                       Operations on reals                            *)
(* -------------------------------------------------------------------- *)
let _Real = fun x -> EcPath.pqname p_Real x

let p_real_opp = _Real id_opp
let p_real_add = _Real id_add
let p_real_sub = _Real id_sub
let p_real_mul = _Real id_mul
let p_real_div = _Real id_div
let p_real_pow = _Real id_pow   
let p_real_le  = _Real id_le
let p_real_lt  = _Real id_lt
let p_real_ge  = _Real id_ge
let p_rle_ge_sym  = _Real "le_ge_sym"

(* -------------------------------------------------------------------- *)
(*                           Finite sets                                *)
(* -------------------------------------------------------------------- *)
let p_FSet = EcPath.pqname p_top "FSet"
let p_fset = EcPath.pqname p_FSet "set"

(* -------------------------------------------------------------------- *)
(*                            Intervals                                 *)
(* -------------------------------------------------------------------- *)
let p_Sum = EcPath.pqname p_top "Sum"
let _Sum  = fun x -> EcPath.pqname p_Sum x

let p_int_intval = _Sum "intval"
let p_int_sum    = _Sum "int_sum"

(* -------------------------------------------------------------------- *)
(*                          Distributions                               *)
(* -------------------------------------------------------------------- *)
let id_Distr = "Distr"
let p_Distr  = EcPath.pqname p_top id_Distr
let _Distr   = fun x -> EcPath.pqname p_Distr x

let p_in_supp = _Distr "in_supp"
let p_mu      = _Pervasive "mu"
let p_mu_x    = _Distr "mu_x"
let p_weight  = _Distr "weight"

let p_dbitstring = List.fold_left EcPath.pqname p_Distr ["Dbitstring"; "dbitstring"]
let p_dinter     = List.fold_left EcPath.pqname p_Distr ["Dinter"; "dinter"]

let s_dbitstring = EcPath.toqsymbol p_dbitstring
let s_dinter     = EcPath.toqsymbol p_dinter

(* -------------------------------------------------------------------- *)
(*                             Booleans                                 *)
(* -------------------------------------------------------------------- *)
let id_Bool = "Bool"
let p_Bool  = EcPath.pqname p_top id_Bool

let p_dbool = List.fold_left EcPath.pqname p_Bool ["Dbool"; "dbool"]
let s_dbool = EcPath.toqsymbol p_dbool

(* -------------------------------------------------------------------- *)
(*                          Logical lemmas                              *)
(* -------------------------------------------------------------------- *)
let p_Logic = EcPath.pqname p_top "Logic" 
let _Logic  = fun x -> EcPath.pqname p_Logic x

let p_cut_lemma     = _Logic "cut_lemma"
let p_false_elim    = _Logic "falseE"
let p_and_elim      = _Logic "andE"
let p_anda_elim     = _Logic "andaE"
let p_and_proj_l    = _Logic "andEl"
let p_and_proj_r    = _Logic "andEr"
let p_or_elim       = _Logic "orE"
let p_ora_elim      = _Logic "oraE"
let p_iff_elim      = _Logic "iffE"
let p_if_elim       = _Logic "ifE"

let p_true_intro    = _Logic "trueI"
let p_and_intro     = _Logic "andI"
let p_anda_intro    = _Logic "andaI"
let p_or_intro_l    = _Logic "orIl"
let p_ora_intro_l   = _Logic "oraIl"
let p_or_intro_r    = _Logic "orIr"
let p_ora_intro_r   = _Logic "oraIr"
let p_iff_intro     = _Logic "iffI"
let p_if_intro      = _Logic "ifI"
let p_eq_refl       = _Logic "eq_refl"
let p_eq_trans      = _Logic "eq_trans"
let p_fcongr        = _Logic "fcongr"
let p_eq_sym        = _Logic "eq_sym"

let p_rewrite_l     = _Logic "rewrite_l"
let p_rewrite_r     = _Logic "rewrite_r"
let p_rewrite_iff_l = _Logic "rewrite_iff_l"
let p_rewrite_iff_r = _Logic "rewrite_iff_r"
let p_rewrite_bool  = _Logic "rewrite_bool"

let p_case_eq_bool  = _Logic "bool_case_eq"

let p_tuple_ind n = 
  if 2 <= n && n <= 9 then
    let name = Format.sprintf "tuple%i_ind" n in
    _Logic name
  else raise Not_found
