(* -------------------------------------------------------------------- *)
open EcUtils
open EcTypes
open EcFol
open EcEnv
open EcAst

open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal

module Sid = EcIdent.Sid

(* -------------------------------------------------------------------- *)
module LowInternal = struct

  let t_finalize h h1 h2 =
     FApi.t_seqs [t_elim_hyp h;
                        t_intros_i [h1;h2];
                        t_apply_hyp h2]

  let t_finalize_ehoare h _h1 _h2 tc =
    t_apply_hyp h tc

 let t_gen_cond ?(t_finalize=t_finalize) side e tc =
   let hyps  = FApi.tc1_hyps tc in
   let fresh = ["&m"; "&m"; "_"; "_"; "_"] in
   let fresh = LDecl.fresh_ids hyps fresh in

   let m1,m2,h,h1,h2 = as_seq5 fresh in

   let t_introm = if is_none side then t_id else t_intros_i [m1] in

   let t_sub b tc =
     FApi.t_on1seq 0
       (EcPhlRCond.t_rcond side b (Zpr.cpos 1))
       (FApi.t_seqs
          [t_introm; EcPhlSkip.t_skip; t_intros_i [m2;h];
           t_finalize h h1 h2; t_simplify])
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
  LowInternal.t_gen_cond None (Inv_ss (ss_inv_of_expr (EcMemory.memory hs.hs_m) e)) tc

(* -------------------------------------------------------------------- *)
let t_ehoare_cond tc =
  let hs = tc1_as_ehoareS tc in
  let (e,_,_) = fst (tc1_first_if tc hs.ehs_s) in
  LowInternal.t_gen_cond ~t_finalize:LowInternal.t_finalize_ehoare
    None (Inv_ss (ss_inv_of_expr (EcMemory.memory hs.ehs_m) e)) tc

(* -------------------------------------------------------------------- *)
let t_bdhoare_cond tc =
  let bhs = tc1_as_bdhoareS tc in
  let (e,_,_) = fst (tc1_first_if tc bhs.bhs_s) in
  LowInternal.t_gen_cond None (Inv_ss (ss_inv_of_expr (EcMemory.memory bhs.bhs_m) e)) tc

(* -------------------------------------------------------------------- *)
let rec t_equiv_cond side tc =
  let hyps = FApi.tc1_hyps tc in
  let es   = tc1_as_equivS tc in
  let ml, mr = fst es.es_ml, fst es.es_mr in

  match side with
  | Some s ->
      let e =
        match s with
        | `Left ->
          let (e,_,_) = fst (tc1_first_if tc es.es_sl) in
          ss_inv_generalize_right (ss_inv_of_expr ml e) mr
        | `Right ->
          let (e,_,_) = fst (tc1_first_if tc es.es_sr) in
          ss_inv_generalize_left (ss_inv_of_expr mr e) ml
      in LowInternal.t_gen_cond side (Inv_ts e) tc

  | None ->
      let el,_,_ = fst (tc1_first_if tc es.es_sl) in
      let er,_,_ = fst (tc1_first_if tc es.es_sr) in
      let el     = ss_inv_generalize_right (ss_inv_of_expr ml el) mr in
      let er     = ss_inv_generalize_left (ss_inv_of_expr mr er) ml in
      let fiff   =
        EcSubst.f_forall_mems_ts_inv es.es_ml es.es_mr
          (map_ts_inv2 f_imp (es_pr es) (map_ts_inv2 f_iff el er)) in

      let fresh = ["hiff";"&m1";"&m2";"h";"h";"h"] in
      let fresh = LDecl.fresh_ids hyps fresh in

      let hiff,m1,m2,h,h1,h2 = as_seq6 fresh in

      let t_aux =
        let rwpt =
          EcCoreGoal.ptlocal
            ~args:[PAMemory m1; PAMemory m2; PASub None]
            hiff in

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
module LowMatchInternal : sig
  val t_gen_match : side option -> FApi.backward
end = struct
  let t_gen_match (side : side option) (tc : tcenv1) : tcenv =
    let hyps   = FApi.tc1_hyps tc in
    let env    = LDecl.toenv hyps in
    let me, st = EcLowPhlGoal.tc1_get_stmt side tc in

    let (e, _), _ = tc1_first_match tc st in
    let _, indt, _ = oget (EcEnv.Ty.get_top_decl e.e_ty env) in
    let indt = oget (EcDecl.tydecl_as_datatype indt) in
    let f = 
      let f = ss_inv_of_expr (EcMemory.memory me) e in
      let pre = tc1_get_pre tc in
      match pre, side with
      | Inv_ts {mr}, Some `Left ->
        Inv_ts (ss_inv_generalize_right f mr)
      | Inv_ts {ml}, Some `Right ->
        Inv_ts (ss_inv_generalize_left f ml)
      | Inv_ss _, _ ->
        Inv_ss f
      | Inv_ts _, None -> tc_error !!tc "expecting a side" in

    let onsub (i : int) (tc : tcenv1) =
      let cname, cargs = List.nth indt.tydt_ctors i in
      let cargs = List.length cargs in

      let tc, names = t_intros_n_x cargs tc in
      let tc = FApi.as_tcenv1 tc in

      let discharge (tc : tcenv1) =
        let+ tc =
          if   Option.is_some side
          then EcLowGoal.t_intros_n 1 tc
          else t_id tc
        in

        let+ tc = EcPhlSkip.t_skip tc in
        let+ tc = EcLowGoal.t_intro_s `Fresh tc in
        let+ tc = EcLowGoal.t_elim_and tc in
        let e = EcEnv.LDecl.fresh_id (FApi.tc1_hyps tc) "e" in

        let+ tc = EcLowGoal.t_intros_i [e] tc in
        let+ tc = EcLowGoal.t_intros_n ~clear:true 1 tc in

        let+ tc =
          let hyps = FApi.tc1_hyps tc in
          let args =
            List.map
              (fun x ->
                 let ty = EcEnv.LDecl.var_by_id x hyps in
                 PAFormula (f_local x ty))
              names in
          EcLowGoal.t_exists_intro_s args tc in

        let+ tc = EcLowGoal.t_symmetry tc in
        let+ tc = EcLowGoal.t_apply_hyp e ~args:[] ~sk:0 tc in

        t_id tc
      in

      let clean (tc : tcenv1) =
        let discharge_pre tc =
          let+ tc =
            if   Option.is_some side
            then EcLowGoal.t_intros_n 2 tc
            else EcLowGoal.t_intros_n 1 tc
          in
          let+ tc = EcLowGoal.t_elim_and tc in
          let+ tc = EcLowGoal.t_intro_s `Fresh tc in
          let+ tc = EcLowGoal.t_elim_and tc in
          let+ tc = EcLowGoal.t_intros_n ~clear:true 1 tc in
          let+ tc = EcLowGoal.t_intro_s `Fresh tc in
          tc
            |> EcLowGoal.t_split
            @! EcLowGoal.t_assumption `Alpha
        in
        let discharge_post tc =
          let+ tc =
            if   Option.is_some side
            then EcLowGoal.t_intros_n 2 tc
            else EcLowGoal.t_intros_n 1 tc
          in
          let t_imp = EcLowGoal.t_intros_n 1 @! EcLowGoal.t_assumption `Alpha in
          let t_iff = EcLowGoal.t_split @! t_imp in
          tc |> FApi.t_or t_imp t_iff
        in

        let pre = oget (EcLowPhlGoal.get_pre (FApi.tc1_goal tc)) in
        let post = oget (EcLowPhlGoal.get_post (FApi.tc1_goal tc)) in

        let pre = map_inv1 (fun pre -> 
          let eq, _, pre = destr_and3 pre in
          f_and eq pre) pre in
        tc
          |> EcPhlConseq.t_conseq pre post
          @+ [discharge_pre; discharge_post; EcLowGoal.t_clears names]
      in

      tc
        |> EcPhlRCond.t_rcond_match side cname (Zpr.cpos 1)
        @+ [discharge; clean]
    in

    let tc = FApi.as_tcenv1 (EcPhlExists.t_hr_exists_intro [f] tc) in
    let tc = FApi.as_tcenv1 (EcPhlExists.t_hr_exists_elim_r ~bound:1 tc) in
    let tc = EcLowGoal.t_elimT_ind `Case tc in

    FApi.t_onalli onsub tc
end

(* -------------------------------------------------------------------- *)
let t_hoare_match (tc : tcenv1) : tcenv =
  let _ : sHoareS = tc1_as_hoareS tc in
  LowMatchInternal.t_gen_match None tc

(* -------------------------------------------------------------------- *)
let t_bdhoare_match (tc : tcenv1) : tcenv =
  let _ : bdHoareS = tc1_as_bdhoareS tc in
  LowMatchInternal.t_gen_match None tc

(* -------------------------------------------------------------------- *)
let t_equiv_match (s : side) (tc : tcenv1) : tcenv =
  let _ : equivS = tc1_as_equivS tc in
  LowMatchInternal.t_gen_match (Some s) tc

(* -------------------------------------------------------------------- *)
let t_equiv_match_same_constr tc =
  let hyps = FApi.tc1_hyps tc in
  let env  = LDecl.toenv hyps in
  let es   = tc1_as_equivS tc in
  let ml, mr = fst es.es_ml, fst es.es_mr in

  let (el, bsl), sl = tc1_first_match tc es.es_sl in
  let (er, bsr), sr = tc1_first_match tc es.es_sr in

  let pl, dt, tyl = oget (EcEnv.Ty.get_top_decl el.e_ty env) in
  let pr, _ , tyr = oget (EcEnv.Ty.get_top_decl er.e_ty env) in

  if not (EcPath.p_equal pl pr) then
    tc_error !!tc "match statements on different inductive types";

  let dt = oget (EcDecl.tydecl_as_datatype dt) in
  let fl = ss_inv_generalize_right (ss_inv_of_expr ml el) mr in
  let fr = ss_inv_generalize_left (ss_inv_of_expr mr er) ml in

  let get_eqv_cond ((c, _), ((cl, _), (cr, _))) =
    let bhl  = List.map (fst_map EcIdent.fresh) cl in
    let bhr  = List.map (fst_map EcIdent.fresh) cr in
    let cop  = EcPath.pqoname (EcPath.prefix pl) c in
    let copl = f_op cop tyl (toarrow (List.snd cl) fl.inv.f_ty) in
    let copr = f_op cop tyr (toarrow (List.snd cr) fr.inv.f_ty) in

    let lhs = map_ts_inv1 (fun fl -> f_eq fl (f_app copl (List.map (curry f_local) bhl) fl.f_ty)) fl in
    let lhs = map_ts_inv1 (f_exists (List.map (snd_map gtty) bhl)) lhs in

    let rhs = map_ts_inv1 (fun fr -> f_eq fr (f_app copr (List.map (curry f_local) bhr) fr.f_ty)) fr in
    let rhs = map_ts_inv1 (f_exists (List.map (snd_map gtty) bhr)) rhs in

    EcSubst.f_forall_mems_ts_inv es.es_ml es.es_mr 
      (map_ts_inv2 f_imp_simpl (es_pr es) (map_ts_inv2 f_iff lhs rhs)) in

  let get_eqv_goal ((c, _), ((cl, bl), (cr, br))) =
    let sb      = Fsubst.f_subst_id in
    let sb, bhl = add_elocals sb cl in
    let sb, bhr = add_elocals sb cr in
    let cop     = EcPath.pqoname (EcPath.prefix pl) c in
    let copl    = f_op cop tyl (toarrow (List.snd cl) fl.inv.f_ty) in
    let copr    = f_op cop tyr (toarrow (List.snd cr) fr.inv.f_ty) in
    let f_ands_simpl' f = f_ands_simpl (List.tl f) (List.hd f) in
    let pre     = map_ts_inv f_ands_simpl'
      [es_pr es; map_ts_inv1 (fun fl -> f_eq fl (f_app copl (List.map (curry f_local) bhl) fl.f_ty)) fl;
        map_ts_inv1 (fun fr -> f_eq fr (f_app copr (List.map (curry f_local) bhr) fr.f_ty)) fr ]
       in

    f_forall
      ( (List.map (snd_map gtty) bhl) @
        (List.map (snd_map gtty) bhr) )
      ( f_equivS (snd es.es_ml) (snd es.es_mr) pre 
        (EcModules.stmt ((s_subst sb bl).s_node @ sl.s_node)) 
        (EcModules.stmt ((s_subst sb br).s_node @ sr.s_node))
        (es_po es))

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
  let ml, mr = fst es.es_ml, fst es.es_mr in

  let (el, bsl), sl = tc1_first_match tc es.es_sl in
  let (er, bsr), sr = tc1_first_match tc es.es_sr in

  let pl, dt, tyl = oget (EcEnv.Ty.get_top_decl el.e_ty env) in
  let pr, _ , tyr = oget (EcEnv.Ty.get_top_decl er.e_ty env) in

  if not (EcPath.p_equal pl pr) then
    tc_error !!tc "match statements on different inductive types";

  if not (EcReduction.EqTest.for_type env el.e_ty er.e_ty) then
    tc_error !!tc "synced match requires matches on the same type";

  let dt = oget (EcDecl.tydecl_as_datatype dt) in
  let fl = ss_inv_generalize_right (ss_inv_of_expr ml el) mr in
  let fr = ss_inv_generalize_left (ss_inv_of_expr mr er) ml in

  let eqv_cond =
    EcSubst.f_forall_mems_ts_inv es.es_ml es.es_mr
      (map_ts_inv2 f_imp_simpl (es_pr es) (map_ts_inv2 f_eq fl fr)) in

  let get_eqv_goal ((c, _), ((cl, bl), (cr, br))) =
    let sb     = f_subst_init () in
    let sb, bh = add_elocals sb cl in

    let sb =
      List.fold_left2
        (fun sb (x, xty) (y, _) ->
          bind_elocal sb y (e_subst sb (e_local x xty)))
        sb cl cr in

    let cop    = EcPath.pqoname (EcPath.prefix pl) c in
    let copl   = f_op cop tyl (toarrow (List.snd cl) fl.inv.f_ty) in
    let copr   = f_op cop tyr (toarrow (List.snd cr) fr.inv.f_ty) in
    let f_ands_simpl' f = f_ands_simpl (List.tl f) (List.hd f) in
    let pre    = map_ts_inv f_ands_simpl'
      [ es_pr es; map_ts_inv1 (fun fl -> f_eq fl (f_app copl (List.map (curry f_local) bh) fl.f_ty)) fl;
        map_ts_inv1 (fun fr -> f_eq fr (f_app copr (List.map (curry f_local) bh) fr.f_ty)) fr ] in

    f_forall
      (List.map (snd_map gtty) bh)
      (f_equivS (snd es.es_ml) (snd es.es_mr) pre
        (EcModules.stmt ((s_subst sb bl).s_node @ sl.s_node))
        (EcModules.stmt ((s_subst sb br).s_node @ sr.s_node))
        (es_po es))

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
