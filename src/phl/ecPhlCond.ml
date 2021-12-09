(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2021 - Inria
 * Copyright (c) - 2012--2021 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcIdent
open EcTypes
open EcModules
open EcFol
open EcEnv

open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal

module Sid = EcIdent.Sid

(* -------------------------------------------------------------------- *)
module LowInternal = struct
 let t_gen_cond side e c tc =
   let hyps  = FApi.tc1_hyps tc in
   let fresh = ["&m"; "&m"; "_"; "_"; "_";"_";"_"] in
   let fresh = LDecl.fresh_ids hyps fresh in

   let m1,m2,h,h1,h2,h3,h4 = as_seq7 fresh in

   let t_introm = if is_none side then t_id else t_intros_i [m1] in

   let t1 =
     FApi.t_or
       (FApi.t_seqs [t_elim_hyp h;
                     t_intros_i [h1;h2];
                     t_apply_hyp h2])
       (t_apply_hyp h) in

   let t2 =
     FApi.t_seqs [t_elim_hyp h;
                  t_intros_i [h1; h2];
                  t_elim_hyp h1;
                  t_intros_i [h3; h4];
                  FApi.t_seqsub t_split
                    [t_apply_hyp h4; t_apply_hyp h2]] in
   let t3 =
     match c with
     | None -> t1
     | Some _ -> FApi.t_or t2 t1 in

   let t_sub b tc =
     FApi.t_on1seq 0
       (EcPhlRCond.t_rcond side b (Zpr.cpos 1) c)
       (FApi.t_seqs
          [t_introm; EcPhlSkip.t_skip; t_intros_i [m2;h]; t3; t_simplify])
       tc
   in
   FApi.t_seqsub
     (EcPhlCase.t_hl_case ~simplify:false e)
     [t_sub true; t_sub false] tc
end

(* -------------------------------------------------------------------- *)
let t_hoare_cond tc =
  let hs = tc1_as_hoareS tc in
  let (e,_,_) = fst (tc1_first_if tc hs.hs_s) in
  LowInternal.t_gen_cond None (form_of_expr (EcMemory.memory hs.hs_m) e) None tc

(* -------------------------------------------------------------------- *)
let t_choare_cond c tc =
  let chs = tc1_as_choareS tc in
  let (e,_,_) = fst (tc1_first_if tc chs.chs_s) in
  let t =
    LowInternal.t_gen_cond None (form_of_expr (EcMemory.memory chs.chs_m) e) c
  in
  match c with
  | None -> t tc
  | Some pr ->
    FApi.t_seqsub
      (EcPhlConseq.t_cHoareS_conseq (f_and chs.chs_pr pr) chs.chs_po)
      [t_id; t_trivial; t] tc

(* -------------------------------------------------------------------- *)
let t_bdhoare_cond tc =
  let bhs = tc1_as_bdhoareS tc in
  let (e,_,_) = fst (tc1_first_if tc bhs.bhs_s) in
  LowInternal.t_gen_cond None (form_of_expr (EcMemory.memory bhs.bhs_m) e) None tc

(* -------------------------------------------------------------------- *)
let rec t_equiv_cond side tc =
  let hyps = FApi.tc1_hyps tc in
  let es   = tc1_as_equivS tc in

  match side with
  | Some s ->
      let e =
        match s with
        | `Left ->
          let (e,_,_) = fst (tc1_first_if tc es.es_sl) in
          form_of_expr (EcMemory.memory es.es_ml) e
        | `Right ->
          let (e,_,_) = fst (tc1_first_if tc es.es_sr) in
          form_of_expr (EcMemory.memory es.es_mr) e
      in LowInternal.t_gen_cond side e None tc

  | None ->
      let el,_,_ = fst (tc1_first_if tc es.es_sl) in
      let er,_,_ = fst (tc1_first_if tc es.es_sr) in
      let el     = form_of_expr (EcMemory.memory es.es_ml) el in
      let er     = form_of_expr (EcMemory.memory es.es_mr) er in
      let fiff   =
        f_forall_mems
          [es.es_ml;es.es_mr]
          (f_imp es.es_pr (f_iff el er)) in

      let fresh = ["hiff";"&m1";"&m2";"h";"h";"h"] in
      let fresh = LDecl.fresh_ids hyps fresh in

      let hiff,m1,m2,h,h1,h2 = as_seq6 fresh in

      let t_aux =
        let rwpt = { pt_head = PTLocal hiff;
                     pt_args = [PAMemory m1; PAMemory m2; PASub None]; } in


        FApi.t_seqs [t_intros_i [m1]    ; EcPhlSkip.t_skip;
                     t_intros_i [m2; h] ; t_elim_hyp h;
                     t_intros_i [h1; h2];
                     FApi.t_seqsub
                       (t_rewrite rwpt (`RtoL, None))
                       [t_apply_hyp h1; t_apply_hyp h2]]
      in
        FApi.t_on1seq 1 (t_cut fiff)
          (t_intros_i_seq [hiff]
             (FApi.t_seqsub
                (t_equiv_cond (Some `Left))
                [FApi.t_seqsub
                   (EcPhlRCond.Low.t_equiv_rcond `Right true (Zpr.cpos 1))
                   [t_aux; t_clear hiff];
                 FApi.t_seqsub
                   (EcPhlRCond.Low.t_equiv_rcond `Right false (Zpr.cpos 1))
                   [t_aux; t_clear hiff]]))
          tc

(* -------------------------------------------------------------------- *)
let t_equiv_match s tc =
  let hyps = FApi.tc1_hyps tc in
  let env  = LDecl.toenv hyps in
  let es   = tc1_as_equivS tc in

  let me, st =
    match s with
    | `Left  -> es.es_ml, es.es_sl
    | `Right -> es.es_mr, es.es_sr in

  let sets st =
    match s with
    | `Left  -> { es with es_sl = st; }
    | `Right -> { es with es_sr = st; } in

  let (e, bs), tl = tc1_first_match tc st in
  let indp, indt, tyinst = oget (EcEnv.Ty.get_top_decl e.e_ty env) in
  let indt = oget (EcDecl.tydecl_as_datatype indt) in
  let f = form_of_expr (EcMemory.memory me) e in

  let do1 ((ids, b), (cname, _)) =
    let subst, lvars =
      add_locals e_subst_id ids in

    let cop = EcPath.pqoname (EcPath.prefix indp) cname in
    let cop = f_op cop tyinst (toarrow (List.snd ids) f.f_ty) in
    let cop =
      let args = List.map (curry f_local) lvars in
      f_app cop args f.f_ty in
    let cop = f_eq f cop in

    f_forall
      (List.map (snd_map gtty) lvars)
      (f_equivS_r
         { (sets (stmt ((s_subst subst b).s_node @ tl.s_node)))
             with es_pr = f_and_simpl cop es.es_pr })

  in

  let concl = List.map do1 (List.combine bs indt.EcDecl.tydt_ctors) in

  FApi.xmutate1 tc (`Match s) concl

(* -------------------------------------------------------------------- *)
let t_equiv_match_same_constr tc =
  let hyps = FApi.tc1_hyps tc in
  let env  = LDecl.toenv hyps in
  let es   = tc1_as_equivS tc in

  let (el, bsl), sl = tc1_first_match tc es.es_sl in
  let (er, bsr), sr = tc1_first_match tc es.es_sr in

  let pl, dt, tyl = oget (EcEnv.Ty.get_top_decl el.e_ty env) in
  let pr, _ , tyr = oget (EcEnv.Ty.get_top_decl er.e_ty env) in

  if not (EcPath.p_equal pl pr) then
    tc_error !!tc "match statements on different inductive types";

  let dt = oget (EcDecl.tydecl_as_datatype dt) in
  let fl = form_of_expr (EcMemory.memory es.es_ml) el in
  let fr = form_of_expr (EcMemory.memory es.es_mr) er in

  let get_eqv_cond ((c, _), ((cl, _), (cr, _))) =
    let bhl  = List.map (fst_map EcIdent.fresh) cl in
    let bhr  = List.map (fst_map EcIdent.fresh) cr in
    let cop  = EcPath.pqoname (EcPath.prefix pl) c in
    let copl = f_op cop tyl (toarrow (List.snd cl) fl.f_ty) in
    let copr = f_op cop tyr (toarrow (List.snd cr) fr.f_ty) in

    let lhs = f_eq fl (f_app copl (List.map (curry f_local) bhl) fl.f_ty) in
    let lhs = f_exists (List.map (snd_map gtty) bhl) lhs in

    let rhs = f_eq fr (f_app copr (List.map (curry f_local) bhr) fr.f_ty) in
    let rhs = f_exists (List.map (snd_map gtty) bhr) rhs in

    f_forall_mems [es.es_ml; es.es_mr] (f_imp_simpl es.es_pr (f_iff lhs rhs)) in

  let get_eqv_goal ((c, _), ((cl, bl), (cr, br))) =
    let sb      = EcTypes.e_subst_id in
    let sb, bhl = EcTypes.add_locals sb cl in
    let sb, bhr = EcTypes.add_locals sb cr in
    let cop     = EcPath.pqoname (EcPath.prefix pl) c in
    let copl    = f_op cop tyl (toarrow (List.snd cl) fl.f_ty) in
    let copr    = f_op cop tyr (toarrow (List.snd cr) fr.f_ty) in
    let pre     = f_ands_simpl
      [ f_eq fl (f_app copl (List.map (curry f_local) bhl) fl.f_ty);
        f_eq fr (f_app copr (List.map (curry f_local) bhr) fr.f_ty) ]
      es.es_pr in

    f_forall
      ( (List.map (snd_map gtty) bhl) @
        (List.map (snd_map gtty) bhr) )
      ( f_equivS_r
          { es with
              es_sl = EcModules.stmt ((s_subst sb bl).s_node @ sl.s_node);
              es_sr = EcModules.stmt ((s_subst sb br).s_node @ sr.s_node);
              es_pr = pre; } )

  in

  let infos =
    (List.combine dt.EcDecl.tydt_ctors (List.combine bsl bsr)) in

  let concl1 = List.map get_eqv_cond infos in
  let concl2 = List.map get_eqv_goal infos in

  FApi.xmutate1 tc `Match (concl1 @ concl2)

(* -------------------------------------------------------------------- *)
let t_equiv_match_eq tc =
  let hyps = FApi.tc1_hyps tc in
  let env  = LDecl.toenv hyps in
  let es   = tc1_as_equivS tc in

  let (el, bsl), sl = tc1_first_match tc es.es_sl in
  let (er, bsr), sr = tc1_first_match tc es.es_sr in

  let pl, dt, tyl = oget (EcEnv.Ty.get_top_decl el.e_ty env) in
  let pr, _ , tyr = oget (EcEnv.Ty.get_top_decl er.e_ty env) in

  if not (EcPath.p_equal pl pr) then
    tc_error !!tc "match statements on different inductive types";

  if not (EcReduction.EqTest.for_type env el.e_ty er.e_ty) then
    tc_error !!tc "synced match requires matches on the same type";

  let dt = oget (EcDecl.tydecl_as_datatype dt) in
  let fl = form_of_expr (EcMemory.memory es.es_ml) el in
  let fr = form_of_expr (EcMemory.memory es.es_mr) er in

  let eqv_cond =
    f_forall_mems [es.es_ml; es.es_mr]
      (f_imp_simpl es.es_pr (f_eq fl fr)) in

  let get_eqv_goal ((c, _), ((cl, bl), (cr, br))) =
    let sb     = { EcTypes.e_subst_id with es_freshen = true; } in
    let sb, bh = EcTypes.add_locals sb cl in

    let sb =
      List.fold_left2
        (fun sb (x, _) (y, _) ->
          { sb with es_loc =
              Mid.add y (oget (Mid.find_opt x sb.es_loc)) sb.es_loc })
        sb cl cr in

    let cop    = EcPath.pqoname (EcPath.prefix pl) c in
    let copl   = f_op cop tyl (toarrow (List.snd cl) fl.f_ty) in
    let copr   = f_op cop tyr (toarrow (List.snd cr) fr.f_ty) in
    let pre    = f_ands_simpl
      [ f_eq fl (f_app copl (List.map (curry f_local) bh) fl.f_ty);
        f_eq fr (f_app copr (List.map (curry f_local) bh) fr.f_ty) ]
      es.es_pr in

    f_forall
      (List.map (snd_map gtty) bh)
      (f_equivS_r
         { es with
             es_sl = EcModules.stmt ((s_subst sb bl).s_node @ sl.s_node);
             es_sr = EcModules.stmt ((s_subst sb br).s_node @ sr.s_node);
             es_pr = pre; } )

  in

  let infos =
    (List.combine dt.EcDecl.tydt_ctors (List.combine bsl bsr)) in

  let concl2 = List.map get_eqv_goal infos in

  FApi.xmutate1 tc `Match ([eqv_cond] @ concl2)

(* -------------------------------------------------------------------- *)
let t_equiv_match infos tc =
  match infos with
  | `DSided `Eq -> t_equiv_match_eq tc
  | `DSided `ConstrSynced -> t_equiv_match_same_constr tc
  | `SSided s -> t_equiv_match s tc
