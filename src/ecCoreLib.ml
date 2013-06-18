(* -------------------------------------------------------------------- *)
let s_get  = "__get"
let s_set  = "__set"
let s_nil  = "__nil"
let s_cons = "::"
let s_abs  = "__abs"

(* -------------------------------------------------------------------- *)
let s_dbool      = (["<top>"; "Bool" ; "Dbool"     ], "dbool")
let s_dbitstring = (["<top>"; "Distr"; "Dbitstring"], "dbitstring")
let s_dinter     = (["<top>"; "Distr"; "Dinter"    ], "dinter")
let s_from_int   = (["<top>"; "Real" ; "FromInt"   ], "from_int")

(* -------------------------------------------------------------------- *)
let id_top       = "<top>"
let id_Pervasive = "Pervasive"
let id_unit      = "unit"
let id_tt        = "tt"
let id_bool      = "bool"
let id_int       = "int"
let id_real      = "real"
let id_distr     = "distr"
let id_cpred     = "cPred"
let id_from_int  = "from_int"

let id_true      = "true"
let id_false     = "false"
let id_not       = "!"
let id_and       = "/\\"
let id_anda      = "&&"
let id_ora       = "||"
let id_or        = "\\/"
let id_imp       = "=>"
let id_iff       = "<=>"
let id_eq        = "="

let id_le        = "<="
let id_lt        = "<"

let id_sum         = "+"
let id_sub         = "-"
let id_prod        = "*"
let id_div         = "/"

let id_in_supp   = "in_supp"
let id_mu        = "mu"
let id_mu_x      = "mu_x"

let p_top         = EcPath.psymbol id_top
let p_Pervasive   = EcPath.pqname p_top id_Pervasive
let _Pervasive id = EcPath.pqname p_Pervasive id

let p_unit       = _Pervasive id_unit
let p_tt         = _Pervasive id_tt
let p_bool       = _Pervasive id_bool
let p_int        = _Pervasive id_int
let p_real       = _Pervasive id_real
let p_distr      = _Pervasive id_distr
let p_cpred      = _Pervasive id_cpred
let p_from_int   = EcPath.fromqsymbol s_from_int

let p_true       = _Pervasive id_true
let p_false      = _Pervasive id_false
let p_not        = _Pervasive id_not
let p_anda       = _Pervasive id_anda 
let p_and        = _Pervasive id_and
let p_ora        = _Pervasive id_ora
let p_or         = _Pervasive id_or
let p_imp        = _Pervasive id_imp
let p_iff        = _Pervasive id_iff
let p_eq         = _Pervasive id_eq

let id_Int       = "Int"
let p_Int        = EcPath.pqname p_top id_Int 
let _Int id      = EcPath.pqname p_Int id

let p_int_le     = _Int  id_le
let p_int_lt     = _Int  id_lt

let id_Real      = "Real"
let p_Real       = EcPath.pqname p_top id_Real
let _Real id     = EcPath.pqname p_Real id

let p_real_le    = _Real id_le
let p_real_lt    = _Real id_lt   
let p_real_sum    = _Real id_sum
let p_real_sub    = _Real id_sub
let p_real_prod   = _Real id_prod
let p_real_div    = _Real id_div   

let id_Distr     = "Distr"
let p_Distr      = EcPath.pqname p_top id_Distr
let _Distr id    = EcPath.pqname p_Distr id

let p_in_supp    = _Distr id_in_supp
let p_mu         = _Pervasive id_mu
let p_mu_x       = _Distr id_mu_x


let p_Logic         = EcPath.pqname p_top "Logic" 
let _Logic    id    = EcPath.pqname p_Logic id

let p_cut_lemma     = _Logic "cut_lemma"
let p_false_elim    = _Logic "false_elim"
let p_and_elim      = _Logic "and_elim"
let p_anda_elim     = _Logic "anda_elim"
let p_and_proj_l    = _Logic "and_proj_l"
let p_and_proj_r    = _Logic "and_proj_r"
let p_or_elim       = _Logic "or_elim"
let p_ora_elim      = _Logic "ora_elim"
let p_iff_elim      = _Logic "iff_elim"
let p_if_elim       = _Logic "if_elim"

let p_true_intro    = _Logic "true_intro"
let p_and_intro     = _Logic "and_intro"
let p_anda_intro    = _Logic "anda_intro"
let p_or_intro_l    = _Logic "or_intro_l"
let p_ora_intro_l   = _Logic "ora_intro_l"
let p_or_intro_r    = _Logic "or_intro_r"
let p_ora_intro_r   = _Logic "ora_intro_r"
let p_iff_intro     = _Logic "iff_intro"
let p_if_intro      = _Logic "if_intro"
let p_eq_refl       = _Logic "eq_refl"
let p_eq_trans      = _Logic "eq_trans"
let p_fcongr        = _Logic "fcongr"

let p_rewrite_l     = _Logic "rewrite_l"
let p_rewrite_r     = _Logic "rewrite_r"
let p_rewrite_iff_l = _Logic "rewrite_iff_l"
let p_rewrite_iff_r = _Logic "rewrite_iff_r"

let p_case_eq_bool  = _Logic "case_eq_bool"

let p_tuple_ind n = 
  if 2 <= n && n <= 9 then
    let name = Format.sprintf "tuple%i_ind" n in
    _Logic name
  else raise Not_found
