(* -------------------------------------------------------------------- *)  
open EcUtils
open EcTypes
open EcModules
open EcFol
open EcBaseLogic
open EcLogic
open EcCorePhl

(* -------------------------------------------------------------------- *)  
class rn_hl_skip = object
  inherit xrule "[hl] skip"
end

let rn_hl_skip = RN_xtd (new rn_hl_skip)

(* -------------------------------------------------------------------- *)  
module LowInternal = struct
  let t_hoare_skip g =
    let concl = get_concl g in
    let hs = destr_hoareS concl in
    if hs.hs_s.s_node <> [] then tacerror NoSkipStmt;
    let concl = f_imp hs.hs_pr hs.hs_po in
    let concl = f_forall_mems [hs.hs_m] concl in
      prove_goal_by [concl] rn_hl_skip g
  
  let t_bdHoare_skip g =
    let concl = get_concl g in
    let bhs = destr_bdHoareS concl in
    if bhs.bhs_s.s_node <> [] then tacerror NoSkipStmt;
    if (bhs.bhs_cmp <> FHeq && bhs.bhs_cmp <> FHge) then
      cannot_apply "skip" "bound must be \">= 1\"";
    let concl = f_imp bhs.bhs_pr bhs.bhs_po in
    let concl = f_forall_mems [bhs.bhs_m] concl in
    let gs = 
      if   f_equal bhs.bhs_bd f_r1
      then [concl] 
      else [f_eq bhs.bhs_bd f_r1; concl]
    in
      prove_goal_by gs rn_hl_skip g
  
  let t_equiv_skip g =
    let concl = get_concl g in
    let es = destr_equivS concl in
    if es.es_sl.s_node <> [] then tacerror NoSkipStmt;
    if es.es_sr.s_node <> [] then tacerror NoSkipStmt;
    let concl = f_imp es.es_pr es.es_po in
    let concl = f_forall_mems [es.es_ml; es.es_mr] concl in
      prove_goal_by [concl] rn_hl_skip g
end

(* -------------------------------------------------------------------- *)  
let t_skip =
  t_hS_or_bhS_or_eS
    ~th: LowInternal.t_hoare_skip
    ~tbh:LowInternal.t_bdHoare_skip
    ~te: LowInternal.t_equiv_skip 
