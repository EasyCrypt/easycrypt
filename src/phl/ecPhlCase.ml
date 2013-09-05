(* --------------------------------------------------------------------- *)
open EcUtils
open EcTypes
open EcFol
open EcBaseLogic
open EcLogic
open EcCorePhl

(* --------------------------------------------------------------------- *)
class rn_hl_case phi =
object
  inherit xrule "[hl] case"

  method phi : form = phi
end

let rn_hl_case phi =
  RN_xtd (new rn_hl_case phi :> xrule)

let t_hoare_case f g =
  let concl = get_concl g in
  let hs = t_as_hoareS concl in
  let concl1 = f_hoareS_r { hs with hs_pr = f_and_simpl hs.hs_pr f } in
  let concl2 = f_hoareS_r { hs with hs_pr = f_and_simpl hs.hs_pr (f_not f) } in
  prove_goal_by [concl1;concl2] (rn_hl_case f) g

let t_bdHoare_case f g =
  let concl = get_concl g in
  let bhs = t_as_bdHoareS concl in
  let concl1 = f_bdHoareS_r 
    { bhs with bhs_pr = f_and_simpl bhs.bhs_pr f } in
  let concl2 = f_bdHoareS_r 
    { bhs with bhs_pr = f_and_simpl bhs.bhs_pr (f_not f) } in
  prove_goal_by [concl1;concl2] (rn_hl_case f) g

let t_equiv_case f g = 
  let concl = get_concl g in
  let es = t_as_equivS concl in
  let concl1 = f_equivS_r { es with es_pr = f_and es.es_pr f } in
  let concl2 = f_equivS_r { es with es_pr = f_and es.es_pr (f_not f) } in
  prove_goal_by [concl1;concl2] (rn_hl_case f) g

let t_hl_case f g =
  t_hS_or_bhS_or_eS
    ~th:(t_hoare_case f) 
    ~tbh:(t_bdHoare_case f)
    ~te:(t_equiv_case f) g 
