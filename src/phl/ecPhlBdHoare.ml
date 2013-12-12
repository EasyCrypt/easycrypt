(* -------------------------------------------------------------------- *)
open EcUtils
open EcFol
open EcBaseLogic
open EcLogic
open EcCorePhl
open EcPhlConseq

(* -------------------------------------------------------------------- *)
class rn_hl_hoare_bd_hoare =
object
  inherit xrule "[hl] hoare-bd-hoare"
end

let rn_hl_hoare_bd_hoare =
  RN_xtd (new rn_hl_hoare_bd_hoare)

(* -------------------------------------------------------------------- *)
(* This are the 4 basic rules                                           *)
let errormsg = "bound is not = 0%r"

let hoare_of_bdhoareS g =
  let concl = get_concl g in
  let bhs = t_as_bdHoareS concl in
  if not (bhs.bhs_cmp = FHeq && f_equal bhs.bhs_bd f_r0) then 
    tacuerror "%s" errormsg;
  let concl = 
    f_hoareS bhs.bhs_m bhs.bhs_pr bhs.bhs_s (f_not bhs.bhs_po) in
  prove_goal_by [concl] rn_hl_hoare_bd_hoare g

let hoare_of_bdhoareF g =
  let concl = get_concl g in
  let bhf = t_as_bdHoareF concl in
  if not (bhf.bhf_cmp = FHeq && f_equal bhf.bhf_bd f_r0) then 
    tacuerror "%s" errormsg;
  let concl = 
    f_hoareF bhf.bhf_pr bhf.bhf_f (f_not bhf.bhf_po) in
  prove_goal_by [concl] rn_hl_hoare_bd_hoare g

let bdhoare_of_hoareS g =
  let concl = get_concl g in
  let hs = t_as_hoareS concl in
  let concl1 = f_bdHoareS hs.hs_m hs.hs_pr hs.hs_s (f_not hs.hs_po) FHeq f_r0 in
  prove_goal_by [concl1] rn_hl_hoare_bd_hoare g

let bdhoare_of_hoareF g =
  let concl = get_concl g in
  let hf = t_as_hoareF concl in
  let concl1 = f_bdHoareF hf.hf_pr hf.hf_f (f_not hf.hf_po) FHeq f_r0 in
  prove_goal_by [concl1] rn_hl_hoare_bd_hoare g

(* -------------------------------------------------------------------- *)
(* The top-level tactic                                                 *)
let t_hoare_bd_hoare g = 
  let concl = get_concl g in
  match concl.f_node with
  | FbdHoareF bhf ->
    if bhf.bhf_cmp = FHeq && f_equal bhf.bhf_bd f_r0 then 
      hoare_of_bdhoareF g
    else 
      t_seq_subgoal (t_bdHoareF_conseq_bd FHeq f_r0)
        [t_try EcPhlTrivial.t_trivial;
         hoare_of_bdhoareF] g

  | FbdHoareS bhs -> 
    if bhs.bhs_cmp = FHeq && f_equal bhs.bhs_bd f_r0 then 
       hoare_of_bdhoareS g
    else 
      t_seq_subgoal (t_bdHoareS_conseq_bd FHeq f_r0)
        [t_try EcPhlTrivial.t_trivial;
         hoare_of_bdhoareS] g
  | FhoareF _ -> bdhoare_of_hoareF g
  | FhoareS _ -> bdhoare_of_hoareS g
  | _ -> tacuerror "a hoare or phoare judgment was expected"
    
