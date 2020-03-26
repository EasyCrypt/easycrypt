(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcTypes
open EcModules
open EcFol
open EcPV

open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal

module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
type bhl_infos_t = (form, ty -> form option, ty -> form) rnd_tac_info
type rnd_infos_t = (pformula, pformula option, pformula) rnd_tac_info
type mkbij_t     = EcTypes.ty -> EcTypes.ty -> EcFol.form

(* -------------------------------------------------------------------- *)
module Core = struct

  (* -------------------------------------------------------------------- *)
  let t_hoare_rnd_r tc =
    let env = FApi.tc1_env tc in
    let hs = tc1_as_hoareS tc in
    let (lv, distr), s = tc1_last_rnd tc hs.hs_s in
    let ty_distr = proj_distr_ty env (e_ty distr) in
    let x_id = EcIdent.create (symbol_of_lv lv) in
    let x = f_local x_id ty_distr in
    let distr = EcFol.form_of_expr (EcMemory.memory hs.hs_m) distr in
    let post = subst_form_lv env (EcMemory.memory hs.hs_m) lv x hs.hs_po in
    let post = f_imp (f_in_supp x distr) post in
    let post = f_forall_simpl [(x_id,GTty ty_distr)] post in
    let concl = f_hoareS_r {hs with hs_s=s; hs_po=post} in
    FApi.xmutate1 tc `Rnd [concl]

  (* -------------------------------------------------------------------- *)
  let wp_equiv_disj_rnd_r side tc =
    let env = FApi.tc1_env tc in
    let es  = tc1_as_equivS tc in
    let m,s =
      match side with
      | `Left  -> es.es_ml, es.es_sl
      | `Right -> es.es_mr, es.es_sr
    in

    (* FIXME: exception when not rnds found *)
    let (lv, distr), s = tc1_last_rnd tc s in
    let ty_distr = proj_distr_ty env (e_ty distr) in

    let x_id = EcIdent.create (symbol_of_lv lv) in
    let x    = f_local x_id ty_distr in

    let distr = EcFol.form_of_expr (EcMemory.memory m) distr in
    let post  = subst_form_lv env (EcMemory.memory m) lv x es.es_po in
    let post  = f_imp (f_in_supp x distr) post in
    let post  = f_forall_simpl [(x_id,GTty ty_distr)] post in
    let post  = f_anda (f_lossless ty_distr distr) post in
    let concl =
      match side with
      | `Left  -> f_equivS_r { es with es_sl=s; es_po=post; }
      | `Right -> f_equivS_r { es with es_sr=s; es_po=post; }
    in
    FApi.xmutate1 tc `Rnd [concl]

  (* -------------------------------------------------------------------- *)
  let wp_equiv_rnd_r bij tc =
    let env = FApi.tc1_env tc in
    let es = tc1_as_equivS tc in
    let (lvL, muL), sl' = tc1_last_rnd tc es.es_sl in
    let (lvR, muR), sr' = tc1_last_rnd tc es.es_sr in
    let tyL = proj_distr_ty env (e_ty muL) in
    let tyR = proj_distr_ty env (e_ty muR) in
    let xL_id = EcIdent.create (symbol_of_lv lvL ^ "L")
    and xR_id = EcIdent.create (symbol_of_lv lvR ^ "R") in
    let xL = f_local xL_id tyL in
    let xR = f_local xR_id tyR in
    let muL = EcFol.form_of_expr (EcMemory.memory es.es_ml) muL in
    let muR = EcFol.form_of_expr (EcMemory.memory es.es_mr) muR in

    let tf, tfinv =
      match bij with
      | Some (f, finv) -> (f tyL tyR, finv tyR tyL)
      | None ->
        if not (EcReduction.EqTest.for_type env tyL tyR) then
          tc_error !!tc "%s, %s"
            "support are not compatible"
            "an explicit bijection is required";
        (EcFol.f_identity ~name:"z" tyL,
         EcFol.f_identity ~name:"z" tyR)
    in

    (*     (∀ x₂, x₂ ∈ ℑ(D₂) ⇒ x₂ = f(f⁻¹(x₂))
     *  && (∀ x₂, x₂ ∈ ℑ(D₂) ⇒ μ(x₂, D₂) = μ(f⁻¹(x₂), D₁))
     *  && (∀ x₁, x₁ ∈ ℑ(D₁) ⇒ f(x₁) ∈ ℑ(D₂) && x₁ = f⁻¹(f(x₁)) && φ(x₁, f(x₁)))
     *)

    let f    t = f_app_simpl tf    [t] tyR in
    let finv t = f_app_simpl tfinv [t] tyL in

    let cond_fbij      = f_eq xL (finv (f xL)) in
    let cond_fbij_inv  = f_eq xR (f (finv xR)) in

    let post = es.es_po in
    let post = subst_form_lv env (EcMemory.memory es.es_ml) lvL xL     post in
    let post = subst_form_lv env (EcMemory.memory es.es_mr) lvR (f xL) post in

    let cond1 = f_imp (f_in_supp xR muR) cond_fbij_inv in
    let cond2 = f_imp (f_in_supp xR muR) (f_eq (f_mu_x muR xR) (f_mu_x muL (finv xR))) in
    let cond3 = f_andas [f_in_supp (f xL) muR; cond_fbij; post] in
    let cond3 = f_imp (f_in_supp xL muL) cond3 in

    let concl = f_andas
      [f_forall_simpl [(xR_id, GTty tyR)] cond1;
       f_forall_simpl [(xR_id, GTty tyR)] cond2;
       f_forall_simpl [(xL_id, GTty tyL)] cond3] in

    let concl = f_equivS_r { es with es_sl=sl'; es_sr=sr'; es_po=concl; } in

    FApi.xmutate1 tc `Rnd [concl]

  (* -------------------------------------------------------------------- *)
  let t_bdhoare_rnd_r tac_info tc =
    let env = FApi.tc1_env tc in
    let bhs = tc1_as_bdhoareS tc in
    let (lv,distr),s = tc1_last_rnd tc bhs.bhs_s in
    let ty_distr = proj_distr_ty env (e_ty distr) in
    let distr = EcFol.form_of_expr (EcMemory.memory bhs.bhs_m) distr in
    let m = fst bhs.bhs_m in
    let mk_event_cond event =
      let v_id = EcIdent.create "v" in
      let v = f_local v_id ty_distr in
      let post_v = subst_form_lv env (EcMemory.memory bhs.bhs_m) lv v bhs.bhs_po in
      let event_v = f_app event [v] tbool in
      let v_in_supp = f_in_supp v distr in
      f_forall_simpl [v_id,GTty ty_distr]
        begin
          match bhs.bhs_cmp with
          | FHle -> f_imps_simpl [v_in_supp;post_v] event_v
          | FHge -> f_imps_simpl [v_in_supp;event_v] post_v
          | FHeq -> f_imp_simpl v_in_supp (f_iff_simpl event_v post_v)
        end
    in
    let f_cmp = match bhs.bhs_cmp with
      | FHle -> f_real_le
      | FHge -> fun x y -> f_real_le y x
      | FHeq -> f_eq
    in
    let is_post_indep =
      let fv = EcPV.PV.fv env m bhs.bhs_po in
      match lv with
      | LvVar (x,_) -> not (EcPV.PV.mem_pv env x fv)
      | LvTuple pvs ->
        List.for_all (fun (x,_) -> not (EcPV.PV.mem_pv env x fv)) pvs
    in
    let is_bd_indep =
      let fv_bd = PV.fv env mhr bhs.bhs_bd in
      let modif_s = s_write env s in
      PV.indep env modif_s fv_bd
    in
    let mk_event ?(simpl=true) ty =
      let x = EcIdent.create "x" in
      if is_post_indep && simpl then f_predT ty
      else match lv with
           | LvVar (pv,_) ->
             f_lambda [x,GTty ty]
               (EcPV.PVM.subst1 env pv m (f_local x ty) bhs.bhs_po)
           | _ -> tc_error !!tc "cannot infer a valid event, it must be provided"
    in
    let bound,pre_bound,binders =
      if is_bd_indep then
        bhs.bhs_bd, f_true, []
      else
        let bd_id = EcIdent.create "bd" in
        let bd = f_local bd_id treal in
        bd, f_eq bhs.bhs_bd bd, [(bd_id,GTty treal)]
    in
    let subgoals = match tac_info, bhs.bhs_cmp with
      | PNoRndParams, FHle ->
        if is_post_indep then
          (* event is true *)
          let concl = f_bdHoareS_r {bhs with bhs_s=s} in
          [concl]
        else
          let event = mk_event ty_distr in
          let bounded_distr = f_real_le (f_mu env distr event) bound in
          let pre = f_and bhs.bhs_pr pre_bound in
          let post = f_anda bounded_distr (mk_event_cond event) in
          let concl = f_hoareS bhs.bhs_m pre s post in
          let concl = f_forall_simpl binders concl in
          [concl]
      | PNoRndParams, _ ->
        if is_post_indep then
          (* event is true *)
          let event = mk_event ty_distr in
          let bounded_distr = f_eq (f_mu env distr event) f_r1 in
          let concl = f_bdHoareS_r
                        {bhs with bhs_s=s; bhs_po=f_and bhs.bhs_po bounded_distr} in
          [concl]
        else
          let event = mk_event ty_distr in
          let bounded_distr = f_cmp (f_mu env distr event) bound in
          let pre = f_and bhs.bhs_pr pre_bound in
          let post = f_anda bounded_distr (mk_event_cond event) in
          let concl = f_bdHoareS_r {bhs with bhs_s=s; bhs_pr=pre; bhs_po=post; bhs_bd=f_r1} in
          let concl = f_forall_simpl binders concl in
          [concl]
      | PSingleRndParam event, FHle ->
          let event = event ty_distr in
          let bounded_distr = f_real_le (f_mu env distr event) bound in
          let pre = f_and bhs.bhs_pr pre_bound in
          let post = f_anda bounded_distr (mk_event_cond event) in
          let concl = f_hoareS bhs.bhs_m pre s post in
          let concl = f_forall_simpl binders concl in
          [concl]
      | PSingleRndParam event, _ ->
          let event = event ty_distr in
          let bounded_distr = f_cmp (f_mu env distr event) bound in
          let pre = f_and bhs.bhs_pr pre_bound in
          let post = f_anda bounded_distr (mk_event_cond event) in
          let concl = f_bdHoareS_r {bhs with bhs_s=s; bhs_pr=pre; bhs_po=post; bhs_cmp=FHeq; bhs_bd=f_r1} in
          let concl = f_forall_simpl binders concl in
          [concl]
      | PMultRndParams ((phi,d1,d2,d3,d4),event), _ ->
        let event = match event ty_distr with
          | None -> mk_event ~simpl:false ty_distr | Some event -> event
        in
        let bd_sgoal = f_cmp (f_real_add (f_real_mul d1 d2) (f_real_mul d3 d4)) bhs.bhs_bd in
        let sgoal1 = f_bdHoareS_r {bhs with bhs_s=s; bhs_po=phi; bhs_bd=d1} in
        let sgoal2 =
          let bounded_distr = f_cmp (f_mu env distr event) d2 in
          let post = f_anda bounded_distr (mk_event_cond event) in
          f_forall_mems [bhs.bhs_m] (f_imp phi post)
        in
        let sgoal3 = f_bdHoareS_r {bhs with bhs_s=s; bhs_po=f_not phi; bhs_bd=d3} in
        let sgoal4 =
          let bounded_distr = f_cmp (f_mu env distr event) d4 in
          let post = f_anda bounded_distr (mk_event_cond event) in
          f_forall_mems [bhs.bhs_m] (f_imp (f_not phi) post) in
        let sgoal5 =
          let f_inbound x = f_anda (f_real_le f_r0 x) (f_real_le x f_r1) in
          f_ands (List.map f_inbound [d1; d2; d3; d4])
        in
        [bd_sgoal;sgoal1;sgoal2;sgoal3;sgoal4;sgoal5]

      | _, _ -> tc_error !!tc "invalid arguments"
    in

    FApi.xmutate1 tc `Rnd subgoals
end (* Core *)

(* -------------------------------------------------------------------- *)
module E = struct exception Abort end

let solve n f tc =
  let tt =
    FApi.t_seqs
      [EcLowGoal.t_intros_n n;
       EcLowGoal.t_solve ~bases:["random"] ~depth:2;
       EcLowGoal.t_fail] in

  let subtc, hd = FApi.newgoal tc f in

  try
    let subtc =
      FApi.t_last
        (fun tc1 ->
          match FApi.t_try_base tt tc1 with
          | `Failure _  -> raise E.Abort
          | `Success tc -> tc)
        subtc
    in (subtc, Some hd)

  with E.Abort -> tc, None

let t_apply_prept pt tc =
  Apply.t_apply_bwd_r (EcProofTerm.pt_of_prept tc pt) tc

(* -------------------------------------------------------------------- *)
let wp_equiv_disj_rnd_r side tc =

  let tc = Core.wp_equiv_disj_rnd_r side tc in
  let es = tc1_as_equivS (FApi.as_tcenv1 tc) in
  let c1, c2 = destr_and es.es_po in
  let newc1 = EcFol.f_forall_mems [es.es_ml; es.es_mr] c1 in

  let subtc = tc in
  let subtc, hdc1 = solve 2 newc1 subtc in

  match hdc1 with
  | None -> tc
  | Some hd ->
    let po = c2 in
    FApi.t_onalli (function
    | 0 -> EcLowGoal.t_trivial ?subtc:None
    | 1 ->
      let open EcProofTerm.Prept in
      let m1  = EcIdent.create "_" in
      let m2  = EcIdent.create "_" in
      let h   = EcIdent.create "_" in
      let h1   = EcIdent.create "_" in
      (t_intros_i [m1; m2; h] @!
       (t_split @+
        [ t_apply_prept (hdl hd @ [amem m1; amem m2]);
          t_intros_i [h1] @! t_apply_hyp h]))

    | _ -> EcLowGoal.t_id)
    (FApi.t_first
      (EcPhlConseq.t_equivS_conseq es.es_pr po)
      subtc)

(* -------------------------------------------------------------------- *)
let wp_equiv_rnd_r bij tc =
  let tc = Core.wp_equiv_rnd_r bij tc in
  let es = tc1_as_equivS (FApi.as_tcenv1 tc) in

  let c1, c2, c3 = destr_and3 es.es_po in
  let (x, xty, c3) = destr_forall1 c3 in
  let ind, (c3, c4) = snd_map destr_and (destr_imp c3) in
  let newc2 = EcFol.f_forall_mems [es.es_ml; es.es_mr] c2 in
  let newc3 = EcFol.f_forall_mems [es.es_ml; es.es_mr]
                (f_forall [x, xty] (f_imp ind c3)) in

  let subtc = tc in
  let subtc, hdc2 = solve 4 newc2 subtc in
  let subtc, hdc3 = solve 4 newc3 subtc in

  let po =
    match hdc2, hdc3 with
    | None  , None   -> None
    | Some _, Some _ -> Some (f_anda c1 (f_forall [x, xty] (f_imp ind c4)))
    | Some _, None   -> Some (f_anda c1 (f_forall [x, xty] (f_imp ind (f_anda c3 c4))))
    | None  , Some _ -> Some (f_andas [c1; c2; f_forall [x, xty] (f_imp ind c4)])
  in

  match po with None -> tc | Some po ->

  let m1  = EcIdent.create "_" in
  let m2  = EcIdent.create "_" in
  let h   = EcIdent.create "_" in
  let h1  = EcIdent.create "_" in
  let h2  = EcIdent.create "_" in
  let x   = EcIdent.create "_" in
  let hin = EcIdent.create "_" in

  FApi.t_onalli (function
    | 0 -> EcLowGoal.t_trivial ?subtc:None
    | 1 ->
      let open EcProofTerm.Prept in

      let t_c2 =
        let pt =
          match hdc2 with
          | None -> hyp h2
          | Some hd -> hdl hd @ [amem m1; amem m2] in
        t_apply_prept pt in

      let t_c3_c4 =
        match hdc3 with
        | None -> t_apply_prept (hyp h)
        | Some hd ->
          let fx = f_local x (gty_as_ty xty) in
          t_intros_i [x; hin] @! t_split
          @+ [ t_apply_prept (hdl hd @ [amem m1; amem m2; aform fx; ahyp hin]);
               t_intros_n 1 @!
                t_apply_prept ((hyp h) @ [aform fx; ahyp hin])]
      in

      let t_case_c2 =
        match hdc2 with
        | None -> t_elim_and @! t_intros_i [h2; h]
        | Some _ -> t_intros_i [h] in

      t_intros_i [m1; m2] @! t_elim_and @! t_intros_i [h1] @! t_case_c2 @! t_split @+
        [ t_apply_prept (hyp h1);
          t_intros_n 1 @! t_split @+
            [ t_c2;
              t_intros_n 1 @! t_c3_c4
            ]
         ]

    | _ -> EcLowGoal.t_id)

    (FApi.t_first
      (EcPhlConseq.t_equivS_conseq es.es_pr po)
      subtc)

(* -------------------------------------------------------------------- *)
let t_equiv_rnd_r side bij_info tc =
  match side with
  | Some side -> wp_equiv_disj_rnd_r side tc
  | None ->
      let bij =
        match bij_info with
        | Some f, Some finv ->  Some (f, finv)
        | Some bij, None | None, Some bij -> Some (bij, bij)
        | None, None -> None
      in
        wp_equiv_rnd_r bij tc


(* -------------------------------------------------------------------- *)
let wp_equiv_disj_rnd = FApi.t_low1 "wp-equiv-disj-rnd" wp_equiv_disj_rnd_r
let wp_equiv_rnd      = FApi.t_low1 "wp-equiv-rnd"      wp_equiv_rnd_r

(* -------------------------------------------------------------------- *)
let t_hoare_rnd   = FApi.t_low0 "hoare-rnd"   Core.t_hoare_rnd_r
let t_bdhoare_rnd = FApi.t_low1 "bdhoare-rnd" Core.t_bdhoare_rnd_r
let t_equiv_rnd   = FApi.t_low2 "equiv-rnd"   t_equiv_rnd_r

(* -------------------------------------------------------------------- *)
let process_rnd side tac_info tc =
  let concl = FApi.tc1_goal tc in

  match side, tac_info with
  | None, PNoRndParams when is_hoareS concl ->
      t_hoare_rnd tc

  | None, _ when is_bdHoareS concl ->
    let tac_info =
      match tac_info with
      | PNoRndParams ->
          PNoRndParams

      | PSingleRndParam fp ->
          PSingleRndParam
            (fun t -> TTC.tc1_process_Xhl_form tc (tfun t tbool) fp)

      | PMultRndParams ((phi, d1, d2, d3, d4), p) ->
          let p t = p |> omap (TTC.tc1_process_Xhl_form tc (tfun t tbool)) in
          let phi = TTC.tc1_process_Xhl_form tc tbool phi in
          let d1  = TTC.tc1_process_Xhl_form tc treal d1 in
          let d2  = TTC.tc1_process_Xhl_form tc treal d2 in
          let d3  = TTC.tc1_process_Xhl_form tc treal d3 in
          let d4  = TTC.tc1_process_Xhl_form tc treal d4 in
          PMultRndParams ((phi, d1, d2, d3, d4), p)

      | _ -> tc_error !!tc "invalid arguments"
    in
      t_bdhoare_rnd tac_info tc

  | _, _ when is_equivS concl ->
    let process_form f ty1 ty2 =
      TTC.tc1_process_prhl_form tc (tfun ty1 ty2) f in

    let bij_info =
      match tac_info with
      | PNoRndParams -> None, None
      | PSingleRndParam f -> Some (process_form f), None
      | PTwoRndParams (f, finv) -> Some (process_form f), Some (process_form finv)
      | _ -> tc_error !!tc "invalid arguments"

    in
      t_equiv_rnd side bij_info tc

  | _ -> tc_error !!tc "invalid arguments"
