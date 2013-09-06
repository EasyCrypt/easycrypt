(* -------------------------------------------------------------------- *)
open EcUtils
open EcMaps
open EcParsetree
open EcLocation
open EcTypes
open EcModules
open EcFol
open EcEnv
open EcReduction
open EcBaseLogic
open EcLogic
open EcHiLogic
open EcCorePhl
open EcCoreHiPhl
open EcCoreHiLogic
open EcPhl

module TT = EcTyping
module UE = EcUnify.UniEnv


(* César says: too much code repetition w.r.t. ecPhl *)
let process_bdHoare_deno info (_,n as g) = 
  let process_cut g (pre,post) = 
    let hyps,concl = get_goal g in
    let cmp, f, bd =
      match concl.f_node with
      | Fapp({f_node = Fop(op,_)}, [f;bd]) when is_pr f &&
          (EcPath.p_equal op EcCoreLib.p_eq || 
             EcPath.p_equal op EcCoreLib.p_real_le ) ->
        let cmp = if EcPath.p_equal op EcCoreLib.p_eq then FHeq else FHle in
        cmp, f, bd
      | Fapp({f_node = Fop(op,_)}, [bd;f]) when is_pr f 
          &&
          (EcPath.p_equal op EcCoreLib.p_eq || 
             EcPath.p_equal op EcCoreLib.p_real_le ) ->
        let cmp = if EcPath.p_equal op EcCoreLib.p_eq then FHeq else FHge in
        cmp, f , bd
      | _ -> cannot_apply "bdHoare_deno" 
        "the conclusion is not a suitable Pr expression" in (* FIXME error message *) 
    let _,f,_,event = destr_pr f in
    let penv, qenv = LDecl.hoareF f hyps in
    let pre  = pre  |> omap_dfl (fun p -> process_form penv p tbool) f_true in
    let post = post |> omap_dfl (fun p -> process_form qenv p tbool) event in
    f_bdHoareF pre f post cmp bd 
  in
  let (juc,an), gs = process_mkn_apply (process_cut g) info g in
  let pre,post =
    let (_,f) = get_node (juc,an) in
    let bhf = t_as_bdHoareF f in
    bhf.bhf_pr, bhf.bhf_po in
  t_on_first (t_use an gs) (t_bdHoare_deno pre post (juc,n))

let process_equiv_deno info (_,n as g) = 
  let process_cut g (pre,post) = 
    let hyps,concl = get_goal g in
    let _op, f1, f2 =
      match concl.f_node with
      | Fapp({f_node = Fop(op,_)}, [f1;f2]) when is_pr f1 && is_pr f2 -> 
        op, f1, f2
      | _ -> cannot_apply "equiv_deno" "" in (* FIXME error message *) 
    let _,fl,_,_ = destr_pr f1 in
    let _,fr,_,_ = destr_pr f2 in
    let penv, qenv = LDecl.equivF fl fr hyps in
    let pre  = pre |> omap_dfl (fun p -> process_form penv p tbool) f_true in
    (* FIXME: Benjamin : below: put a better default event instead of f_true *)
    let post = post |> omap_dfl (fun p -> process_form qenv p tbool) f_true in
    f_equivF pre fl fr post in
  let (juc,an), gs = process_mkn_apply (process_cut g) info g in
  let pre,post =
    let (_,f) = get_node (juc,an) in
    let ef = t_as_equivF f in
    ef.ef_pr, ef.ef_po in
  t_on_first (t_use an gs) (t_equiv_deno pre post (juc,n))
  
let process_ppr (phi1,phi2) g =
  let hyps,concl = get_goal g in
  let ef = t_as_equivF concl in
  let _penv,qenv = LDecl.equivF ef.ef_fl ef.ef_fr hyps in
  let phi1 = process_form_opt qenv phi1 None in
  let phi2 = process_form_opt qenv phi2 None in
  (* TODO: check for type unification *)
  let ty = f_ty phi1 in
  t_ppr ty phi1 phi2 g


let process_hoare_bd_hoare g = t_hoare_bd_hoare g
let process_prbounded = t_prbounded
let process_prfalse = t_prfalse
let process_bdeq = t_bdeq

let process_eqobs_in (geq', ginv, eqs') g = 
  let env, hyps, concl = get_goal_e g in
  let ienv = LDecl.inv_memenv hyps in
  let es = t_as_equivS concl in
  let ml, mr =  fst es.es_ml, fst es.es_mr in
 
  let toeq ml mr f = 
    try EcPV.Mpv2.of_form env ml mr f 
    with _ -> 
      let ppe = EcPrinting.PPEnv.ofenv env in
      tacuerror "cannot recognize %a as a set of equalities" 
        (EcPrinting.pp_form ppe) f in

  let geq =
    match geq' with
    | None -> toeq mleft mright f_true
    | Some geq' ->
      let geq = process_form ienv geq' tbool in
      set_loc geq'.pl_loc (toeq mleft mright) geq in

  let ginv = ginv |> omap_dfl (fun f -> process_form ienv f tbool) f_true in
  let ifvl = EcPV.PV.fv env ml ginv in
  let ifvr = EcPV.PV.fv env mr ginv in

  let eqs = 
    match eqs' with 
    | None -> 
      begin 
        try EcPV.Mpv2.needed_eq env ml mr es.es_po 
        with _ -> tacuerror "cannot infer the set of equalities" 
      end
    | Some eqs' -> 
      let eqs = process_prhl_formula g eqs' in
      set_loc eqs'.pl_loc (toeq ml mr) eqs in

  let _, _, (log,_), _ = 
    EcPV.eqobs_in env
      (EcPhl.eqobs_inF env geq (ginv,ifvl,ifvr))
      { query = []; forproof = Mf.empty } es.es_sl es.es_sr eqs (ifvl,ifvr) in
    
  let onF _ fl fr eqo = 
    match find_eqobs_in_log log fl fr eqo with
    | Some (eqo,spec) -> (), eqo, spec 
    | None -> assert false in

  let t_eqobs eqs g =
    let concl = get_concl g in
    let es = t_as_equivS concl in
    let ml, mr = fst es.es_ml, fst es.es_mr in
    let post = EcPV.Mpv2.to_form ml mr eqs ginv in
    let pre = es.es_pr in
    t_seq_subgoal 
      (EcPhlConseq.t_equivS_conseq pre post)
      [ t_trivial;
        t_trivial;
        (fun g -> 
          t_on_last (t_try (t_seq EcPhlSkip.t_skip t_trivial))
            (t_eqobs_inS onF eqs ginv g))] 
      g in
   
  let tocut = 
    Mf.fold (fun spec eori l ->
      match eori with
      | EORI_unknown None -> spec :: l
      | _ -> l) log.forproof [] in
 
  let forproof = ref log.forproof in

  let rec t_cut_spec l g = 
    match l with
    | [] -> t_id None g
    | spec :: l ->
      let hyps = get_hyps g in
      let id = LDecl.fresh_id hyps "H" in
      forproof := Mf.add spec (EORI_unknown (Some id)) !forproof;
      t_seq_subgoal (t_cut spec)
        [ t_id None;
          t_seq (t_intros_i [id]) (t_cut_spec l)] g in
 
  let t_rec g = 
    let concl = get_concl g in
    match Mf.find_opt concl !forproof with
    | Some (EORI_adv geq) ->
      let gs =
        EcPhlFun.FunAbsLow.t_equivF_abs
          (EcPV.Mpv2.to_form mleft mright geq ginv) g in
      t_on_firsts t_trivial 2 gs 
    | Some (EORI_fun eqs) ->
      t_seq EcPhlFun.FunDefLow.t_equivF_fun_def
        (t_eqobs eqs) g 
    | Some (EORI_unknown (Some id)) ->
      t_hyp id g
    | _ -> t_fail g in
  
  t_on_last 
    (t_seq (t_eqobs eqs) (t_repeat t_rec))
    (t_cut_spec tocut g) 

(* -------------------------------------------------------------------- *)
let process_phl loc ptac g =
  let t =
    match ptac with
    | Pfun_def                  -> EcPhlFun.t_fun_def
    | Pfun_abs f                -> EcPhlFun.process_fun_abs f
    | Pfun_upto info            -> EcPhlFun.process_fun_upto info 
    | Pfun_to_code              -> EcPhlFun.t_fun_to_code 
    | Pskip                     -> EcPhlSkip.t_skip
    | Papp (dir, k, phi, f)     -> EcPhlApp.process_app dir k phi f
    | Pwp k                     -> EcPhlWp.t_wp k
    | Psp k                     -> EcPhlSp.t_sp k
    | Prcond (side, b, i)       -> EcPhlRCond.t_rcond side b i
    | Pcond side                -> EcPhlCond.process_cond side
    | Pwhile (side, (phi, vopt))-> EcPhlWhile.process_while side phi vopt
    | Pfission info             -> EcPhlLoopTx.process_fission info
    | Pfusion info              -> EcPhlLoopTx.process_fusion info
    | Punroll info              -> EcPhlLoopTx.process_unroll info
    | Psplitwhile info          -> EcPhlLoopTx.process_splitwhile info
    | Pcall (side, info)        -> EcPhlCall.process_call side info
    | Pswap info                -> EcPhlSwap.process_swap info
    | Pinline info              -> EcPhlInline.process_inline info
    | Pcfold info               -> EcPhlCodeTx.process_cfold info
    | Pkill info                -> EcPhlCodeTx.process_kill info
    | Palias info               -> EcPhlCodeTx.process_alias info
    | Prnd (side, info)         -> EcPhlRnd.process_rnd side info
    | Pconseq (nm,info)         -> EcPhlConseq.process_conseq nm info
    | Phr_exists_elim           -> EcPhlExists.t_hr_exists_elim
    | Phr_exists_intro fs       -> EcPhlExists.process_exists_intro fs
    | Pexfalso                  -> EcPhlExfalso.t_exfalso
    | Pbdhoaredeno info         -> process_bdHoare_deno info
    | PPr (phi1,phi2)           -> process_ppr (phi1,phi2)
    | Pfel (at_pos,info)        -> EcPhlFel.process_fel at_pos info
    | Pequivdeno info           -> process_equiv_deno info
    | Phoare | Pbdhoare         -> process_hoare_bd_hoare
    | Pprbounded                -> process_prbounded
    | Pprfalse                  -> process_prfalse
    | Ppr_rewrite s             -> EcPhlPrRw.t_pr_rewrite s 
    | Pbdeq                     -> process_bdeq
    | Peqobs_in info            -> process_eqobs_in info
    | Ptrans_stmt info          -> EcPhlTrans.process_equiv_trans info
  in
    set_loc loc t g
