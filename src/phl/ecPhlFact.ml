open EcModules
open EcFol
open EcBaseLogic
open EcLogic

class rn_hl_bd_equiv = object
  inherit xrule "[hl] bd equiv"
end
let rn_hl_bd_equiv = RN_xtd (new rn_hl_bd_equiv :> xrule)

let t_bd_equivS side pr po g = 
  let concl = get_concl g in
  let es = destr_equivS concl in
  let m,s,s' = 
    if side then es.es_ml, es.es_sl,es.es_sr 
    else es.es_mr, es.es_sr, es.es_sl in
  if s'.s_node <> [] then 
    tacuerror "the other statement should be empty";
  let subst = Fsubst.f_subst_mem mhr (fst m) in
  let prs, pos = subst pr, subst po in
  let g1 = f_bdHoareS m pr s po FHeq f_r1 in
  let tac = prove_goal_by [g1] rn_hl_bd_equiv in
  t_seq_subgoal (EcPhlConseq.t_equivS_conseq_nm prs pos)
   [t_logic_trivial;
    t_logic_trivial;
    tac] g 

let process_bd_equiv (side,pr,po) g = 
  let hyps,concl = get_goal g in
  let es = destr_equivS concl in
  let m = if side then es.es_ml else es.es_mr in
  let env = EcEnv.LDecl.push_active (mhr,snd m) hyps in
  let pr = EcCoreHiLogic.process_form env pr EcTypes.tbool in
  let po = EcCoreHiLogic.process_form env po EcTypes.tbool in
  t_bd_equivS side pr po g


