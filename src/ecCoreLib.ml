(* -------------------------------------------------------------------- *)
let s_get  = "__get"
let s_set  = "__set"
let s_nil  = "__nil"
let s_cons = "::"
let s_abs  = "__abs"

(* -------------------------------------------------------------------- *)
let s_dbool      = (["<top>"; "Distr"; "Dbool"     ], "dbool")
let s_dbitstring = (["<top>"; "Distr"; "Dbitstring"], "dbitstring")
let s_dinter     = (["<top>"; "Distr"; "Dinter"    ], "dinter")
let s_from_int   = (["<top>"; "Real" ; "FromInt"   ], "from_int")

(* -------------------------------------------------------------------- *)
let id_top       = "<top>"
let id_pervasive = "Pervasive"
let id_unit      = "unit"
let id_tt        = "tt"
let id_bool      = "bool"
let id_int       = "int"
let id_Int       = "Int"
let id_real      = "real"
let id_distr     = "distr"

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

let id_leq       = "<="
let id_lt       = "<"


let p_top        = EcPath.extend None id_top
let p_pervasive  = EcPath.extend (Some p_top) id_pervasive
let pervasive id = EcPath.extend (Some p_pervasive) id

let top_int id     = EcPath.extend (Some (EcPath.extend (Some p_top) id_Int)) id



let p_unit       = pervasive id_unit
let p_tt         = pervasive id_tt
let p_bool       = pervasive id_bool
let p_int        = pervasive id_int
let p_real       = pervasive id_real
let p_distr      = pervasive id_distr

let p_true       = pervasive id_true
let p_false      = pervasive id_false
let p_not        = pervasive id_not
let p_anda       = pervasive id_anda 
let p_and        = pervasive id_and
let p_ora        = pervasive id_ora
let p_or         = pervasive id_or
let p_imp        = pervasive id_imp
let p_iff        = pervasive id_iff
let p_eq         = pervasive id_eq

let p_leq        = top_int id_leq
let p_lt         = top_int id_lt


let p_logic      = EcPath.pqname p_top "Logic" 
let p_cut_lemma  = EcPath.pqname p_logic "cut_lemma"
let p_false_elim = EcPath.pqname p_logic "false_elim"
let p_and_elim   = EcPath.pqname p_logic "and_elim"
let p_anda_elim  = EcPath.pqname p_logic "anda_elim"
let p_or_elim    = EcPath.pqname p_logic "or_elim"
let p_ora_elim   = EcPath.pqname p_logic "ora_elim"
let p_iff_elim   = EcPath.pqname p_logic "iff_elim"
let p_if_elim    = EcPath.pqname p_logic "if_elim"

let p_true_intro  = EcPath.pqname p_logic "true_intro"
let p_and_intro   = EcPath.pqname p_logic "and_intro"
let p_anda_intro  = EcPath.pqname p_logic "anda_intro"
let p_or_intro_l  = EcPath.pqname p_logic "or_intro_l"
let p_ora_intro_l = EcPath.pqname p_logic "ora_intro_l"
let p_or_intro_r  = EcPath.pqname p_logic "or_intro_r"
let p_ora_intro_r = EcPath.pqname p_logic "ora_intro_r"
let p_iff_intro   = EcPath.pqname p_logic "iff_intro"
let p_if_intro    = EcPath.pqname p_logic "if_intro"
let p_eq_refl     = EcPath.pqname p_logic "eq_refl"

let p_rewrite_l     = EcPath.pqname p_logic "rewrite_l"
let p_rewrite_r     = EcPath.pqname p_logic "rewrite_r"
let p_rewrite_iff_l = EcPath.pqname p_logic "rewrite_iff_l"
let p_rewrite_iff_r = EcPath.pqname p_logic "rewrite_iff_r"

let p_case_eq_bool  = EcPath.pqname p_logic "case_eq_bool"
