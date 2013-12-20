(* -------------------------------------------------------------------- *)
open EcParsetree
open EcBaseLogic
open EcTypes
open EcFol
open EcLogic

(* -------------------------------------------------------------------- *)
class rn_hl_hoare_rnd : object
  inherit xrule
end

(* -------------------------------------------------------------------- *)
type hl_infos_t = (form, form, form) rnd_tac_info

class rn_hl_equiv_rnd : hl_infos_t -> object
  inherit xrule

  method infos : hl_infos_t
end

(* -------------------------------------------------------------------- *)
type bhl_infos_t = (form, ty -> form option, ty -> form) rnd_tac_info

class rn_hl_bhl_rnd : bhl_infos_t -> object
  inherit xrule

  method infos : bhl_infos_t
end

(* -------------------------------------------------------------------- *)
val t_hoare_rnd : tactic
val t_bd_hoare_rnd : bhl_infos_t -> tactic
val wp_equiv_rnd : ((EcTypes.ty -> EcTypes.ty -> EcFol.form) *
                    (EcTypes.ty -> EcTypes.ty -> EcFol.form)) option -> tactic
val wp_equiv_disj_rnd : bool -> tactic

(* -------------------------------------------------------------------- *)
val process_rnd : tac_side -> (pformula, pformula option, pformula) rnd_tac_info -> tactic
