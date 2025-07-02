(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcCoreGoal.FApi
open EcMatching.Position
open EcAst

(* -------------------------------------------------------------------- *)
type bhl_infos_t = (ss_inv, ty -> ss_inv option, ty -> ss_inv) rnd_tac_info
type rnd_infos_t = (pformula, pformula option, pformula) rnd_tac_info
type mkbij_t     = EcTypes.ty -> EcTypes.ty -> ts_inv

(* -------------------------------------------------------------------- *)
val wp_equiv_disj_rnd : side -> backward
val wp_equiv_rnd      : (mkbij_t pair) option -> backward

(* -------------------------------------------------------------------- *)
type semrndpos = (bool * codepos1) doption

val t_hoare_rnd   : backward
val t_bdhoare_rnd : bhl_infos_t -> backward
val t_equiv_rnd   : ?pos:semrndpos -> oside -> (mkbij_t option) pair -> backward

(* -------------------------------------------------------------------- *)
val process_rnd : oside -> psemrndpos option -> rnd_infos_t -> backward

(* -------------------------------------------------------------------- *)
val process_rndsem : reduce:bool -> oside -> pcodepos1 -> backward
