
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
    (* FIXME catch exception *)
    Mpv2.of_form env (fst es.es_ml) (fst es.es_mr) in
  es, es.es_sl, es.es_sr, of_form es.es_pr, of_form es.es_po 

let destr_eagerS s s' f = 
  let es = destr_equivS f in
  let c, c' = es.es_sl, es.es_sr in
  (* FIXME catch exception and assert *)
  let s1,c = EcModules.s_split (List.length s.s_node) c in
  let c',s1' = EcModules.s_split (List.length c'.s_node - List.length s'.s_node) c' in
  assert (List.all2 i_equal s1 s.s_node);
  assert (List.all2 i_equal s1' s'.s_node);
  es, stmt c, stmt c'

let get_hSS' hyps h = 
  (* FIXME catch exception *)
  let tH = LDecl.lookup_hyp_by_id h hyps in
  tH, destr_eqobsS (LDecl.toenv hyps) tH 

(* This ensure condition (e) of the eager_seq rule *)
let compat env modS modS' eqR eqXs =
  (* FIXME assert *)
  let check_pv x1 x2 _ = 
    assert (Mpv2.mem x1 x2 eqXs ||
      (not (PV.mem_pv env x1 modS) && not (PV.mem_pv env x2 modS'))) in
  let check_glob m = 
    assert (Mpv2.mem_glob m eqXs ||
      (not (PV.mem_glob env m modS) && not (PV.mem_glob env m modS'))) in
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
  (* check (d) *)assert (Mpv2.subset eqIs seqR); 
  (* check (e) *)compat env (s_write env s) (s_write env s') seqR eqXs;
  (* FIXME catch exception of s_split *)
  let eqO2 = Mpv2.eq_refl (PV.fv env (fst eC.es_mr) eC.es_po) in
  let c1,c2 = EcModules.s_split i c in
  let c1',c2' = EcModules.s_split j c' in
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
           t_seq (t_clear (EcIdent.Sid.singleton a))
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

(* eager while:
   (a) ={I} => e{1} = e{2}
   (b) S;c1 ~ S';c1' : ={I} /\ e{1} ==> ={I}
   (c)  c' ~ c'    : ={I.2} ==> ={I.2}
   (d) forall b &2, S  : e = b ==> e = b
   (e) ={I} => ={Is}
   (f) compat S S' R Xs 
   (h) S ~ S' : ={Is} ==> ={Xs}
   --------------------------------------------------
   S;while e do c ~ while e' do c';S' : ={I} ==> ={I} /\ !e{1}
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
  assert (n1.s_node = [] && n2.s_node = []);
  let eqI = eC.es_pr in
  let seqI = Mpv2.of_form env (fst eC.es_ml) (fst eC.es_mr) eqI in
  let e1 = form_of_expr (fst eC.es_ml) e in
  let e2 = form_of_expr (fst eC.es_mr) e' in
  assert (f_equal eC.es_po (f_and eqI (f_not e1)));
  (* check (e) *)assert (Mpv2.subset eqIs seqI); 
  (* check (f) *)compat env (s_write env s) (s_write env s') seqI eqXs;
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
  t_on_first (t_hyp h) (prove_goal_by [tH;a;b;c] rn_eager_while g)
  
let process_while info  g = 
  let gs, h = process_info info g in
  t_on_last (t_eager_while h) gs



  




      
