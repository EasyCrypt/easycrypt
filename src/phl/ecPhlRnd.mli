(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcTypes
open EcFol
open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)
type chl_infos_t = (form, form option, form) rnd_tac_info
type bhl_infos_t = (form, ty -> form option, ty -> form) rnd_tac_info
type rnd_infos_t = (pformula, pformula option, pformula) rnd_tac_info
type mkbij_t     = EcTypes.ty -> EcTypes.ty -> EcFol.form

(* -------------------------------------------------------------------- *)
val wp_equiv_disj_rnd : side -> backward
val wp_equiv_rnd      : (mkbij_t pair) option -> backward

(* -------------------------------------------------------------------- *)
val t_hoare_rnd   : backward
val t_bdhoare_rnd : bhl_infos_t -> backward
val t_equiv_rnd   : ?pos:semrndpos -> oside -> (mkbij_t option) pair -> backward

(* -------------------------------------------------------------------- *)
val process_rnd : oside -> semrndpos option -> rnd_infos_t -> backward

(* -------------------------------------------------------------------- *)
val process_rndsem : reduce:bool -> oside -> codepos1 -> backward
