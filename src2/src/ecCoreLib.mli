(* --------------------------------------------------------------------- *)
(*           predefined string                                           *)
(* ----------------------------------------------------------------------*)
val s_get  : string
val s_set  : string
val s_nil  : string
val s_cons : string


(* --------------------------------------------------------------------- *)
(*           predefined path                                             *)
(* ----------------------------------------------------------------------*)
open EcPath
val id_top       : EcIdent.t
val p_top        : path
val id_pervasive : EcIdent.t
val p_pervasive  : path
val p_unit       : path
val p_bool       : path
val p_int        : path
val p_real       : path
val p_bitstring  : path

val p_list       : path
val p_nil        : path
val p_cons       : path



val p_true       : path
val p_false      : path

val p_not        : path
val p_and        : path
val p_or         : path
val p_imp        : path
val p_iff        : path
val p_eq         : path



