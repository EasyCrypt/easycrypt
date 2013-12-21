open EcTypes
open EcFol
open EcModules
open EcCorePhl
open EcLogic

let error () = 
  tacuerror "don't known what to do automatically"

let t_auto_rnd_hoare g = 
  EcPhlRnd.t_hoare_rnd g

let prnd_info = 
  (EcParsetree.PSingleRndParam (fun ty ->
    let id = EcIdent.create "x" in
    f_lambda [id,GTty ty] f_true
   )) 

let t_auto_rnd_phoare g = 
  let concl = get_concl g in
  let hs = t_as_bdHoareS concl in
  match List.rev (hs.bhs_s.s_node) with
  | {i_node = Srnd _} :: _ ->
    EcPhlRnd.t_bd_hoare_rnd prnd_info g 
  | _ -> error ()

let t_auto_rnd_equiv g = 
  let env,_,concl = get_goal_e g in
  let es = t_as_equivS concl in
  match List.rev (es.es_sl.s_node), List.rev (es.es_sr.s_node) with
  | {i_node = Srnd (_,e1)} :: _, {i_node = Srnd (_,e2)}::_ when 
      (EcReduction.EqTest.for_type env e1.e_ty e2.e_ty) ->
    EcPhlRnd.wp_equiv_rnd None g
  | {i_node = Srnd _} :: _, _ ->
    EcPhlRnd.wp_equiv_disj_rnd true g
  | _, {i_node = Srnd _} :: _ ->
    EcPhlRnd.wp_equiv_disj_rnd false g
  | _ -> error ()

let t_auto_rnd = 
  t_hS_or_bhS_or_eS 
    ?th:(Some t_auto_rnd_hoare) 
    ?tbh:(Some t_auto_rnd_phoare)
    ?te:(Some t_auto_rnd_equiv) 

let rec t_phl_auto g =
  t_lseq [
    EcPhlWp.t_wp None;
    t_lor [t_seq t_auto_rnd t_phl_auto;
           EcPhlSkip.t_skip;
           t_id None ]] g

let t_auto = 
  let subtc = 
    t_lor [EcPhlTauto.t_hoare_true;
           EcPhlTauto.t_core_exfalso;
           EcPhlPr.t_prbounded false;
           t_phl_auto]
  in
  t_try
    (t_lseq [t_try t_assumption;
             t_progress (t_id None);
             t_try t_assumption; 
             subtc; t_logic_trivial])



  



    


