(* -------------------------------------------------------------------- *)
let s_get  = "__get"
let s_set  = "__set"
let s_nil  = "__nil"
let s_cons = "::"
let s_abs  = "__abs"

(* -------------------------------------------------------------------- *)
let s_dbool      = (["<top>"; "distr"; "Dbool"     ], "dbool")
let s_dbitstring = (["<top>"; "distr"; "Dbitstring"], "dbitstring")
let s_dinter     = (["<top>"; "distr"; "Dinter"    ], "dinter")
let s_from_int   = (["<top>"; "real" ; "FromInt"   ], "from_int")

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

