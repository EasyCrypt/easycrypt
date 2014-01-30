
open EcUtils
open EcLocation
open EcTypes
open EcModules
open EcFol
open EcEnv
open EcBaseLogic
open EcLogic
open EcPV
open EcCorePhl

let destr_eqobsS env f = 
  let es = destr_equivS f in
  let of_form =
    try Mpv2.of_form env (fst es.es_ml) (fst es.es_mr) 
    with Not_found -> 
      tacuerror "can not reconize a set of equalities"
  in
  es, es.es_sl, es.es_sr, of_form es.es_pr, of_form es.es_po 

let destr_eagerS s s' f = 
  let es = destr_equivS f in
  let c, c' = es.es_sl, es.es_sr in
  let s1,c = s_split "eager" (List.length s.s_node) c in
  let c',s1' = 
    s_split "eager" (List.length c'.s_node - List.length s'.s_node) c' in
  if not (List.all2 i_equal s1 s.s_node) then
    tacuerror "the head of the left statement is not the good one";
  if not (List.all2 i_equal s1' s'.s_node) then
    tacuerror "the tail of the right statement is not the good one";
  es, stmt c, stmt c'

let get_hSS' hyps h = 
  let tH = LDecl.lookup_hyp_by_id h hyps in
  tH, destr_eqobsS (LDecl.toenv hyps) tH 

(* This ensure condition (d) and (e) of the eager_seq rule *)
let compat env modS modS' eqR eqIs eqXs =
  if not (Mpv2.subset eqIs eqR) then begin
    let ppe = EcPrinting.PPEnv.ofenv env in
    let eqR = Mpv2.to_form mleft mright eqR f_true in
    let eqIs = Mpv2.to_form mleft mright eqIs f_true in
    tacuerror "%a should be include in %a"
      (EcPrinting.pp_form ppe) eqIs (EcPrinting.pp_form ppe) eqR
  end; 
  let check_pv x1 x2 _ = 
    if not (Mpv2.mem x1 x2 eqXs ||
              (not (PV.mem_pv env x1 modS) && not (PV.mem_pv env x2 modS')))
    then
      let ppe = EcPrinting.PPEnv.ofenv env in
      tacuerror 
        "equality of %a and %a should be ensured by the swapping statement"
        (EcPrinting.pp_pv ppe) x1 (EcPrinting.pp_pv ppe) x2 in
  let check_glob m = 
    if not (Mpv2.mem_glob m eqXs ||
              (not (PV.mem_glob env m modS) && not (PV.mem_glob env m modS'))) 
    then 
      let ppe = EcPrinting.PPEnv.ofenv env in
      tacuerror 
        "equality of %a should be ensured by the swapping statement"
        (EcPrinting.pp_topmod ppe) m in
  Mpv2.iter check_pv check_glob eqR 

let process_info info g =
  let hyps = EcLogic.get_hyps g in
  match info with
  | EcParsetree.LE_done h -> t_id None g, fst (LDecl.lookup_hyp (unloc h) hyps)
  | EcParsetree.LE_todo (h,s1,s2,eqIs, eqXs) ->
    let hyps,concl = get_goal g in
    let es    = t_as_equivS concl in
    let eqIs  = EcCoreHiPhl.process_prhl_formula g eqIs in
    let eqXs  = EcCoreHiPhl.process_prhl_formula g eqXs in
    let s1    = EcCoreHiPhl.process_prhl_stmt true g s1 in
    let s2    = EcCoreHiPhl.process_prhl_stmt false g s2 in
    let f     = f_equivS es.es_ml es.es_mr eqIs s1 s2 eqXs in
    let h     = LDecl.fresh_id hyps (unloc h) in
    t_on_last (EcLogic.t_intros_i [h]) (t_cut f g), h

(*
eager_seq: 
 (a)  c1;S ~ S;c1' : P ==> ={R}   
 (b)  c2;S ~ S;c2' : ={R} ==> Q
 (c)  c2' ~ c2'    : ={R.2} ==> ={Q.2}
 (d)  ={R} => ={Is}
 (e)  compat S S' R Xs 
      (i.e. ={R} => forall modS modS', ={Xs{modS,modS'}} => ={R{modS,modS'}} )
 (h)  S ~ S' : ={Is} ==> ={Xs}
--------------------------------------------------------------------------------
  c1;c2;S ~ S;c1';c2' : P ==> Q

*)

class rn_eager_seq =
object
  inherit xrule "[eager] seq"
end
let rn_eager_seq = RN_xtd (new rn_eager_seq :> xrule)
  
let t_eager_seq i j eqR h g = 
  let env, hyps, concl = get_goal_e g in
  (* h is a proof of (h) *)
  let tH, (_, s, s', eqIs, eqXs) = get_hSS' hyps h in
  let eC, c, c' = destr_eagerS s s' concl in
  let seqR = Mpv2.of_form env (fst eC.es_ml) (fst eC.es_mr) eqR in
  (* check (d) and (e) *)
  compat env (s_write env s) (s_write env s') seqR eqIs eqXs;
  (* FIXME catch exception of s_split *)
  let eqO2 = Mpv2.eq_refl (PV.fv env (fst eC.es_mr) eC.es_po) in
  let c1,c2 = s_split "eager_seq" i c in
  let c1',c2' = s_split "eager_seq" j c' in
  let to_form eq =  Mpv2.to_form (fst eC.es_ml) (fst eC.es_mr) eq f_true in
  let a = f_equivS_r {eC with
    es_sl = stmt (s.s_node@c1); 
    es_sr = stmt (c1'@s'.s_node); 
    es_po = eqR; } in
  let b = f_equivS_r {eC with
    es_pr = eqR;
    es_sl = stmt (s.s_node@c2); 
    es_sr = stmt (c2'@s'.s_node); } in
  let c = f_equivS_r { eC with
    es_ml = (fst eC.es_ml, snd eC.es_mr);
    es_pr = to_form (Mpv2.eq_fv2 seqR);
    es_sl = stmt c2';
    es_sr = stmt c2';
    es_po = to_form eqO2 } in
  t_on_first (t_hyp h) (prove_goal_by [tH;a;b;c] rn_eager_seq g)
  
let process_seq info (i,j) eqR g = 
  let eqR   = EcCoreHiPhl.process_prhl_form tbool g eqR in
  let gs, h = process_info info g in
  t_on_last (t_eager_seq i j eqR h) gs

(* eager if: 
   (a) P => e{1} = e{2}
   (b) S;c1 ~ S';c1' : P /\ e{1} ==> Q
   (c) S;c2 ~ S';c2' : P /\ !e{1} ==> Q
   (d) forall b &2, S  : P /\ e = b ==> e = b
--------------------------------------------------------------------------
   S;if e then c1 else c2 ~ if e' then c1' else c2';S' : P ==> Q

REMARK : This rule is implemented in term of other tactic ....
*)

let t_eager_if g =
  let _, hyps, concl = get_goal_e g in
  let es = destr_equivS concl in
  let (e,_,_),s = s_last_if "eager if" es.es_sl in
  let (e',_,_),_ = s_first_if "eager if" es.es_sr in
  let el = form_of_expr (fst es.es_ml) e in
  let e'r = form_of_expr (fst es.es_mr) e' in
  let eq = f_eq el e'r in
  let (m1,m2,a,h1,h2,h3,h4) = 
    match LDecl.fresh_ids hyps ["&m";"&m";"H";"H";"H";"H";"H"] with
    | [m1;m2;a;h1;h2;h3;h4] -> m1,m2,a,h1,h2,h3,h4
    | _ -> assert false in
  (* FIXME : use generalize_mem instead *)
  let aT = 
    f_forall [mleft,GTmem (snd es.es_ml); mright, GTmem (snd es.es_mr)]
      (f_imp es.es_pr eq) in
  let e0 = form_of_expr mhr e in
  let b = EcIdent.create "b1" in
  let eqb = f_eq e0 (f_local b tbool) in
  let sub = Fsubst.f_bind_mem Fsubst.f_subst_id mleft mhr in
  let sub = Fsubst.f_bind_mem sub mright m2 in
  let p = Fsubst.f_subst sub es.es_pr in
  let bT =  f_forall [m2, GTmem (snd(es.es_mr)); b, GTty tbool]
      (f_hoareS (mhr,snd es.es_ml) (f_and p eqb) s eqb) in
  let at = (List.length s.s_node + 1) in
  let e2 = form_of_expr m2 e' in
  let eq2 = f_eq e0 e2 in
  let tac0 g = 
    let hyps,concl = get_goal g in
    let bd,_ = decompose_forall concl in
    let h = LDecl.fresh_id hyps "H" in
    t_lseq [
      t_intros_i (List.map (fun _ -> EcIdent.create "_") bd);
      t_intros_i [h];
      t_rewrite_hyp `LtoR h [];
      t_hyp h4] g in
        
  let tac1 = 
    t_seq (t_intros_i [m2])
      (t_seq_subgoal 
         (EcPhlConseq.t_hoareS_conseq_nm (f_and p eq2) eq2)
         [ t_lseq [t_intros_i [m1;h2];t_elim_hyp h2;t_intros_i [h3;h4];tac0];
           t_lseq [t_intros_i [m1;h2];t_elim_hyp h2;
                   t_intros_i [h3;h4]; t_hyp h3];
           gen_t_apply_hyp (fun _ _ x -> x) a [AAmem m1; AAform e2]
         ]) in 

  t_seq_subgoal (t_cut aT)
    [t_id None; (* a *)
     t_seq (t_intros_i [a])
       (t_seq_subgoal 
          (EcPhlConseq.t_equivS_conseq (f_and es.es_pr eq) es.es_po)
          [t_seq (t_intros_i [m1;m2;h1])
              (t_seq_subgoal t_split 
                 [t_hyp h1;
                  t_seq 
                    (gen_t_apply_hyp (fun _ _ x -> x) a
                       [AAmem m1;AAmem m2;AAnode])
                    (t_hyp h1)]);
           t_split;
           t_seq (t_clear a)
             (t_seq_subgoal (t_cut bT)
                [ t_id None;
                  t_seq (t_intros_i [a])
                    (t_seq_subgoal (EcPhlCond.t_equiv_cond (Some false))
                       [t_seq_subgoal 
                           (EcPhlRCond.Low.t_equiv_rcond true true  at) 
                           [tac1; t_id None];
                        t_seq_subgoal 
                          (EcPhlRCond.Low.t_equiv_rcond true false at)
                          [tac1; t_id None]
                       ]) 
                ])
          ])]
    g

let process_if = t_eager_if

(* eager while:
   (a) ={I} => e{1} = e{2}
   (b) S;c ~ c';S' : ={I} /\ e{1} ==> ={I}
   (c)  c' ~ c'    : ={I.2} ==> ={I.2}
   (d) forall b &2, S  : e = b ==> e = b
   (e) ={I} => ={Is}
   (f) compat S S' I Xs 
   (h) S ~ S' : ={Is} ==> ={Xs}
   --------------------------------------------------
   S;while e do c ~ while e' do c';S' : ={I} ==> ={I,Xs} /\ !e{1}
*)

class rn_eager_while =
object
  inherit xrule "[eager] while"
end
let rn_eager_while = RN_xtd (new rn_eager_while :> xrule)
  
let t_eager_while h g = 
  let env, hyps, concl = get_goal_e g in
  (* h is a proof of (h) *)
  let tH, (_, s, s', eqIs, eqXs) = get_hSS' hyps h in
  let eC, wc, wc' = destr_eagerS s s' concl in
  let (e,c),(e',c'),n1,n2 = EcCorePhl.s_first_whiles "eager while" wc wc' in
  if not (n1.s_node = [] && n2.s_node = []) then
    tacuerror "can not apply eager while, unexpected statements";
  let eqI = eC.es_pr in
  let seqI = Mpv2.of_form env (fst eC.es_ml) (fst eC.es_mr) eqI in
  let e1 = form_of_expr (fst eC.es_ml) e in
  let e2 = form_of_expr (fst eC.es_mr) e' in
  let post = Mpv2.to_form (fst eC.es_ml) (fst eC.es_mr) 
               (Mpv2.union seqI eqXs) (f_not e1) in
  (* check (e) and (f) *)
  compat env (s_write env s) (s_write env s') seqI eqIs eqXs;
  let to_form eq =  Mpv2.to_form (fst eC.es_ml) (fst eC.es_mr) eq f_true in
  let a = 
    f_forall [mleft,GTmem (snd eC.es_ml); mright, GTmem (snd eC.es_mr)]
      (f_imp eqI (f_eq e1 e2)) in
  let b = f_equivS_r {eC with
    es_pr = f_and_simpl eqI e1;
    es_sl = stmt (s.s_node@c.s_node); 
    es_sr = stmt (c'.s_node@s'.s_node); 
    es_po = eqI; } in
  let eqI2 = to_form (Mpv2.eq_fv2 seqI) in 
  let c = f_equivS_r { eC with
    es_ml = (fst eC.es_ml, snd eC.es_mr);
    es_pr = eqI2;
    es_sl = c';
    es_sr = c';
    es_po = eqI2 } in
  t_seq_subgoal (EcPhlConseq.t_equivS_conseq eqI post)
   [ t_logic_trivial;
     t_logic_trivial;
     fun g -> 
      t_on_first (t_hyp h) (prove_goal_by [tH;a;b;c] rn_eager_while g) ] g
  
let process_while info  g = 
  let gs, h = process_info info g in
  t_on_last (t_eager_while h) gs

(* eager fun def :
  S and S' depend only of global (* This should be an invariant of the typing *)
  S;f.body;result = f.res; ~ S';f'.body;result' = f'.res; : P ==> Q{res{1}<- result, res{2} <- result'}
  -------------------------
   S, f ~ f', S' : P ==> Q
*)

class rn_eager_fun_def =
object
  inherit xrule "[eager] fun def"
end
let rn_eager_fun_def = RN_xtd (new rn_eager_fun_def :> xrule)

let t_eager_fun_def g = 
  let env, _hyps, concl = get_goal_e g in
  let eg = destr_eagerF concl in
  let fl, fr = 
    NormMp.norm_xfun env eg.eg_fl,  NormMp.norm_xfun env eg.eg_fr in
  EcPhlFun.check_concrete env fl; EcPhlFun.check_concrete env fr;

  let memenvl,(fsigl,fdefl),memenvr,(fsigr,fdefr),env = Fun.equivS fl fr env in
  let extend mem fdef = 
    match fdef.f_ret with
    | None -> f_tt, mem, fdef.f_body 
    | Some e ->
      let v = {v_name = "result"; v_type = e.e_ty } in
      let mem, s = EcCorePhl.fresh_pv mem v in
      let f = EcMemory.xpath mem in
      let x = EcTypes.pv_loc f s in
      f_pvar x e.e_ty (fst mem), mem,
      s_seq fdef.f_body (stmt [i_asgn(LvVar(x,e.e_ty), e)]) in
  let el,meml, sfl = extend memenvl fdefl in
  let er,memr, sfr = extend memenvr fdefr in
  let ml, mr = EcMemory.memory meml, EcMemory.memory memr in
  let s = 
    PVM.add env (pv_res fl) ml el 
    (PVM.add env (pv_res fr) mr er PVM.empty) in 
  let post = PVM.subst env s eg.eg_po in
  let s = EcPhlFun.FunDefLow.subst_pre env fl fsigl ml PVM.empty in
  let s = EcPhlFun.FunDefLow.subst_pre env fr fsigr mr s in
  let pre = PVM.subst env s eg.eg_pr in

  (* TODO B : the pre should be substitued *)
  let cond = f_equivS_r { 
    es_ml = meml;
    es_mr = memr;
    es_sl = s_seq eg.eg_sl sfl;
    es_sr = s_seq sfr eg.eg_sr;
    es_pr = pre;
    es_po = post;
  } in
  prove_goal_by [cond] rn_eager_fun_def g
 
  
let process_fun_def  = t_eager_fun_def
  
(* eager fun abs : 
  S and S' depend only of global (* This should be an invariant of the typing *)
   (a) ={I} => e{1} = e{2}
   for each oracles o o':
        o and o' do not modify (glob A) (this is implied by (f) )
    (b) S,o ~ o',S' : ={I,params} ==> ={I,res} 
    (c) o'~ o' : ={I.2, o'.params} ==> ={I.2, res}
   (e) ={I} => ={Is}
   (f) compat S S' I Xs 
   (h) S ~ S' : ={Is} ==> ={Xs}
   glob A not in I (* this is checked in EcPhlFun.equivF_abs_spec *)
   S S' do not modify glob A
---------------------------------------------------
  S, A.f{o} ~ A.f(o'), S' : ={I,glob A,A.f.params} ==> ={I,glob A,res}
 
Remark : ={glob A} is not required in pre condition when A.f is an initializer 
*)

class rn_eager_fun_abs =
object
  inherit xrule "[eager] fun abs"
end
let rn_eager_fun_abs = RN_xtd (new rn_eager_fun_abs :> xrule)

let t_eager_fun_abs eqI h g =
  let env, hyps, concl = get_goal_e g in
  let tH, (_, s, s', eqIs, eqXs) = get_hSS' hyps h in  
  let eg = t_as_eagerF concl in
  if not (s_equal s eg.eg_sl && s_equal s' eg.eg_sr) then
    tacuerror "can not reconize the swapping statement";
  let fl, fr = eg.eg_fl, eg.eg_fr in
  let pre,post,sg = EcPhlFun.FunAbsLow.equivF_abs_spec env fl fr eqI in
  let do1 og sg = 
    let ef = destr_equivF og in
    let torefl f = 
      Mpv2.to_form mleft mright (Mpv2.eq_refl (PV.fv env mright f)) f_true in
    f_eagerF ef.ef_pr s ef.ef_fl ef.ef_fr s' ef.ef_po ::
      f_equivF (torefl ef.ef_pr) ef.ef_fr ef.ef_fr (torefl ef.ef_po) ::
      sg in
  let sg = List.fold_right do1 sg [] in
  let seqI = Mpv2.of_form env mleft mright eqI in
  (* check (e) and (f)*)
  compat env (s_write env s) (s_write env s') seqI eqIs eqXs;
  (* TODO : check that S S' do not modify glob A *)
  let tac g' = 
    t_on_first (t_hyp h) 
      (prove_goal_by (tH::sg) rn_eager_fun_abs g') in
  t_on_last tac (EcPhlConseq.t_eagerF_conseq pre post g)
  
let process_fun_abs info eqI g = 
  let hyps, _ = get_goal g in
  let env = LDecl.inv_memenv hyps in
  let eqI  = EcCoreHiLogic.process_form env eqI tbool in
  let gs, h = process_info info g in
  t_on_last (t_eager_fun_abs eqI h) gs
  
(* eager call :
   S,f ~ f',S' : fpre ==> fpost 
   S do not write a 
   -----------------------------------
   S;x = f(a) ~ x' = f'(a');S' : wp_call fpre fpost post ==> post
*)
class rn_eager_call =
object
  inherit xrule "[eager] call"
end
let rn_eager_call = RN_xtd (new rn_eager_call :> xrule)

let t_eager_call fpre fpost g =
  let env, hyps, concl = get_goal_e g in
  let es = t_as_equivS concl in
  let (lvl,fl,argsl), s = s_last_call "eager call" es.es_sl in
  let (lvr,fr,argsr), s' = s_first_call "eager call" es.es_sr in
  let sw = s_write env s in
  let sw' = s_write env s' in
  let check_a e = 
    let er = e_read env PV.empty e in
    let diff = PV.interdep env sw er in 
    if not (PV.is_empty diff) then 
      tacuerror "eager call: the s statement write %a" (PV.pp env) diff in
  List.iter check_a argsl;
  let ml = EcMemory.memory es.es_ml in
  let mr = EcMemory.memory es.es_mr in
  let modil = PV.union (f_write env fl) sw in
  let modir = PV.union (f_write env fr) sw' in 
  let post = EcPhlCall.wp2_call env fpre fpost (lvl,fl,argsl) modil
     (lvr,fr,argsr) modir ml mr es.es_po hyps in
  let f_concl = f_eagerF fpre s fl fr s' fpost in
  let concl   = f_equivS_r 
    { es with es_sl = stmt []; es_sr = stmt []; es_po=post } in
  prove_goal_by [f_concl;concl] rn_eager_call g

let check_only_global env s = 
  let sw = s_write env s in
  let sr = s_read env s in
  let check_glob v _ =
    if is_loc v then
      let ppe = EcPrinting.PPEnv.ofenv env in
      tacuerror "Swapping statement should use only global variables : %a" 
        (EcPrinting.pp_pv ppe) v
  in
  let check_mp _ = () in
  PV.iter check_glob check_mp sw;
  PV.iter check_glob check_mp sr
        
let process_call info (_,n as g) =
  let process_cut g info = 
    match info with 
    | EcParsetree.CI_spec (fpre,fpost) ->
      let env,hyps,concl = get_goal_e g in
      let es = t_as_equivS concl in
      let (_,fl,_), s = s_last_call "eager call" es.es_sl in
      let (_,fr,_), s' = s_first_call "eager call" es.es_sr in
      check_only_global env s; check_only_global env s';
      let penv, qenv = LDecl.equivF fl fr hyps in
      let fpre  = EcCoreHiLogic.process_form penv fpre tbool in
      let fpost = EcCoreHiLogic.process_form qenv fpost tbool in
      f_eagerF fpre s fl fr s' fpost 
    | _ -> tacuerror "do not known what to do with this kind of info" in

  let (juc,an), gs = EcCoreHiLogic.process_mkn_apply (process_cut g) info g in
  let t_call g =
    let (_,f) = get_node (juc, an) in
    let eg = t_as_eagerF f in
    t_eager_call eg.eg_pr eg.eg_po g in
  t_seq_subgoal t_call [t_use an gs; t_id None] (juc, n)


(***************************************************************************)
(* This part of the code is for automatic application of eager rule as for *)
(* eqobs_in                                                                *)
(***************************************************************************)

let eager env s s' inv eqIs eqXs c c' eqO =
  let modi = s_write env s in
  let modi' = s_write env s' in
  let readi = s_read env s in

  let check_args args =
    let read = List.fold_left (e_read env) PV.empty args in
    if not (PV.indep env modi read) then raise EqObsInError in
    
  let check_swap_s i =
    let m = is_write env PV.empty [i] in
    let r = is_read env PV.empty [i] in
    let t = PV.indep env m modi && 
      PV.indep env m readi && PV.indep env modi r in
    if not t then raise EqObsInError in

  let rev st = List.rev st.s_node in

  let remove lvl lvr eqs =
    let aux eqs (pvl,tyl) (pvr,tyr) = 
      if (EcReduction.EqTest.for_type env tyl tyr) then
        Mpv2.remove env pvl pvr eqs
      else raise EqObsInError in

    match lvl, lvr with
    | LvVar xl, LvVar xr -> aux eqs xl xr 
    | LvTuple ll, LvTuple lr when List.length ll = List.length lr->
      List.fold_left2 aux eqs ll lr
    | LvMap((pl,tysl), pvl, el, tyl),
        LvMap((pr,tysr), pvr, er,tyr) when EcPath.p_equal pl pr &&
      List.all2  (EcReduction.EqTest.for_type env) (tyl::tysl) (tyr::tysr) ->
      add_eqs env (Mpv2.remove env pvl pvr eqs) el er
    | _, _ -> raise EqObsInError in

  let oremove lvl lvr eqs = 
    match lvl, lvr with
    | None, None -> eqs
    | Some lvl, Some lvr -> remove lvl lvr eqs 
    | _, _ -> raise EqObsInError in


  let rec s_eager fhyps rsl rsr eqo =
    match rsl, rsr with
    | [], _ -> [], rsr, fhyps, eqo
    | _, [] -> rsl, [], fhyps, eqo
    | il::rsl', ir::rsr' ->
      match (try Some (i_eager fhyps il ir eqo) with _ -> None) with
      | None -> rsl, rsr, fhyps, eqo
      | Some (fhyps, eqi) -> 
        (* we ensure that the seq rule can be apply *)
        let eqi2 = i_eqobs_in_refl env ir (Mpv2.fv2 eqo) in
        if not (PV.subset eqi2 (Mpv2.fv2 eqi)) then raise EqObsInError;
        compat env modi modi' eqi eqIs eqXs;
        s_eager fhyps rsl' rsr' eqi
  and i_eager fhyps il ir eqo = 
    match il.i_node, ir.i_node with
    | Sasgn(lvl,el), Sasgn(lvr,er) | Srnd(lvl,el), Srnd(lvr,er) ->
      check_swap_s il;
      let eqnm = Mpv2.split_nmod modi modi' eqo in
      let eqm  = Mpv2.split_mod modi modi' eqo in
      if not (Mpv2.subset eqm eqXs) then raise EqObsInError;
      let eqi = Mpv2.union eqIs eqnm in
      fhyps, add_eqs env (remove lvl lvr eqi) el er
    | Scall(lvl,fl,argsl), Scall(lvr,fr,argsr) 
      when List.length argsl = List.length argsr ->
      check_args argsl;
      let eqo = oremove lvl lvr eqo in
      let modl = PV.union modi (f_write env fl) in
      let modr = PV.union modi' (f_write env fr) in
      let eqnm = Mpv2.split_nmod modl modr eqo in
      let outf = Mpv2.split_mod  modl modr eqo in
      Mpv2.check_glob outf;
      let fhyps, inf = f_eager fhyps fl fr outf in
      let eqi = 
        List.fold_left2 (add_eqs env) (Mpv2.union eqnm inf) argsl argsr in
      fhyps, eqi

    | Sif(el,stl,sfl), Sif(er,str,sfr) ->
      check_args [el];
      let r1,r2,fhyps1, eqs1 = s_eager fhyps (rev stl) (rev str) eqo in
      if r1 <> [] || r2 <> [] then raise EqObsInError;
      let r1,r2, fhyps2, eqs2 = s_eager fhyps1 (rev sfl) (rev sfr) eqo in
      if r1 <> [] || r2 <> [] then raise EqObsInError;
      let eqi = Mpv2.union eqs1 eqs2 in
      let eqe = add_eqs env eqi el er in
      fhyps2, eqe 

    | Swhile(el,sl), Swhile(er,sr2) ->
      check_args [el]; (* ensure condition (d) *)
      let sl, sr = rev sl, rev sr2 in
      let rec aux eqo = 
        let r1,r2,fhyps, eqi = s_eager fhyps sl sr eqo in
        if r1 <> [] || r2 <> [] then raise EqObsInError;
        if Mpv2.subset eqi eqo then fhyps, eqo
        else aux (Mpv2.union eqi eqo) in
      let fhyps, eqi = aux (Mpv2.union eqIs (add_eqs env eqo el er)) in
      (* by construction condition (a), (b) and (c) are satisfied *)
      compat env modi modi' eqi eqIs eqXs; (* ensure (e) and (f) *)
      (* (h) is assumed *)
      fhyps, eqi

    | Sassert el, Sassert er -> 
      check_args [el];
      let eqnm = Mpv2.split_nmod modi modi' eqo in
      let eqm  = Mpv2.split_mod modi modi' eqo in
      if not (Mpv2.subset eqm eqXs) then raise EqObsInError;
      let eqi = Mpv2.union eqIs eqnm in
      fhyps, add_eqs env eqi el er
    | Sabstract _, Sabstract _ -> assert false (* FIXME *)
    | _, _ -> raise EqObsInError 
  and f_eager (fhyps:(EcPath.xpath * EcPath.xpath * EcPV.Mpv2.t) list) fl fr out = 
    let fl, fr = NormMp.norm_xfun env fl, NormMp.norm_xfun env fr in
    let rec aux fhyps = 
      match fhyps with
      | [] -> [fl,fr,out]
      | (fl',fr',out') :: fhyps ->
        if EcPath.x_equal fl fl' && EcPath.x_equal fr fr' then
          (fl,fr, Mpv2.union out out')::fhyps
        else (fl',fr',out')::aux fhyps in
    aux fhyps, inv in
 
  s_eager [] (rev c) (rev c') eqO

class rn_eager_auto =
object
  inherit xrule "[eager] auto"
end
let rn_eager_auto = RN_xtd (new rn_eager_auto :> xrule)

let t_eager h inv g =
  let env, hyps, concl = get_goal_e g in
  let _, (_, s, s', eqIs, eqXs) = get_hSS' hyps h in
  check_only_global env s; check_only_global env s';
  let eC, c, c' = destr_eagerS s s' concl in
  let eqinv = Mpv2.of_form env mleft mright inv in
  let eqO = Mpv2.of_form env mleft mright eC.es_po in
  let c1,c1',fhyps,eqi = 
    eager env s s' eqinv eqIs eqXs c c' eqO in
  if c1 <> [] || c1' <> [] then tacuerror "not able to apply eager";
  let dof (fl,fr,eqo) = 
    let defl = Fun.by_xpath fl env in
    let defr = Fun.by_xpath fr env in
    let sigl, sigr = defl.f_sig, defr.f_sig in
    let eq_res = f_eqres fl sigl.fs_ret mleft fr sigr.fs_ret mright in
    let post = Mpv2.to_form mleft mright eqo eq_res in
    let eq_params = 
      f_eqparams fl sigl.fs_arg sigl.fs_anames mleft 
        fr sigr.fs_arg sigr.fs_anames mright in
    let pre = f_and_simpl eq_params inv in
    f_eagerF pre s fl fr s' post in
  let concl = 
    f_equivS_r { eC with es_sl = stmt []; es_sr = stmt []; 
      es_po = Mpv2.to_form mleft mright eqi f_true } in
  let concls = List.map dof fhyps in
  prove_goal_by (concl::concls) rn_eager_auto g

let process_eager info inv g = 
  let hyps = get_hyps g in
  let penv = LDecl.inv_memenv hyps in
  let inv  = EcCoreHiLogic.process_form penv inv tbool in
  let gs, h = process_info info g in
  t_on_last (t_eager h inv) gs


      

