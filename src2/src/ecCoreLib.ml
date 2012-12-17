let s_get  = "get"
let s_set  = "set"
let s_nil  = "[]"
let s_cons = "::"

(* -------------------------------------------------------------------- *)
let id_top       = EcIdent.create "<top>"
let id_pervasive = EcIdent.create "Pervasive"
let id_unit      = EcIdent.create "unit"
let id_bool      = EcIdent.create "bool"
let id_int       = EcIdent.create "int"
let id_real      = EcIdent.create "real"
let id_bitstring = EcIdent.create "bitstring"
let id_list      = EcIdent.create "list"
let id_map       = EcIdent.create "map"

let id_true      = EcIdent.create "true"
let id_false     = EcIdent.create "false"
let id_not       = EcIdent.create "!"
let id_and       = EcIdent.create "&&"
let id_or        = EcIdent.create "||"
let id_imp       = EcIdent.create "=>"
let id_iff       = EcIdent.create "<=>"
let id_eq        = EcIdent.create "="

let p_top        = EcPath.extend None id_top
let p_pervasive  = EcPath.extend (Some p_top) id_pervasive
let pervasive id = EcPath.extend (Some p_pervasive) id

let p_unit       = pervasive id_unit
let p_bool       = pervasive id_bool
let p_int        = pervasive id_int
let p_real       = pervasive id_real
let p_bitstring  = pervasive id_bitstring
let p_list       = pervasive id_list
let p_map        = pervasive id_map

let p_true       = pervasive id_true
let p_false      = pervasive id_false
let p_not        = pervasive id_not 
let p_and        = pervasive id_and
let p_or         = pervasive id_or
let p_imp        = pervasive id_imp
let p_iff        = pervasive id_iff
let p_eq         = pervasive id_eq

