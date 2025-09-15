(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcAst
open EcTypes
open EcModules
open EcFol
open EcPV
open EcSubst

open EcMatching.Position
open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal

module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
type bhl_infos_t = (ss_inv, ty -> ss_inv option, ty -> ss_inv) rnd_tac_info
type rnd_infos_t = (pformula, pformula option, pformula) rnd_tac_info
type mkbij_t     = EcTypes.ty -> EcTypes.ty -> ts_inv
type semrndpos   = (bool * codepos1) doption

(* -------------------------------------------------------------------- *)
module Core = struct

  (* -------------------------------------------------------------------- *)
  let t_hoare_rnd_r tc =
    let env = FApi.tc1_env tc in
    let hs = tc1_as_hoareS tc in
    let m = fst hs.hs_m in
    let (lv, distr), s = tc1_last_rnd tc hs.hs_s in
    let ty_distr = proj_distr_ty env (e_ty distr) in
    let x_id = EcIdent.create (symbol_of_lv lv) in
    let x = {m; inv=f_local x_id ty_distr} in
    let distr = EcFol.ss_inv_of_expr m distr in
    let post = subst_form_lv env lv x (hs_po hs) in
    let post = map_ss_inv2 f_imp (map_ss_inv2 f_in_supp x distr) post in
    let post = map_ss_inv1 (f_forall_simpl [(x_id,GTty ty_distr)]) post in
    let concl = f_hoareS (snd hs.hs_m) (hs_pr hs) s post in
    FApi.xmutate1 tc `Rnd [concl]

  (* -------------------------------------------------------------------- *)
  let t_ehoare_rnd_r tc =
    let env = FApi.tc1_env tc in
    let hs = tc1_as_ehoareS tc in
    let (lv, distr), s = tc1_last_rnd tc hs.ehs_s in
    let ty_distr = proj_distr_ty env (e_ty distr) in
    let x_id = EcIdent.create (symbol_of_lv lv) in
    let x = f_local x_id ty_distr in
    let m = fst hs.ehs_m in
    let distr = EcFol.ss_inv_of_expr m distr in
    let post = subst_form_lv env lv {m;inv=x} (ehs_po hs) in
    let post = map_ss_inv2 (f_Ep ty_distr) distr 
      (map_ss_inv1 (f_lambda [(x_id,GTty ty_distr)]) post) in
    let concl = f_eHoareS (snd hs.ehs_m) (ehs_pr hs) s post in
    FApi.xmutate1 tc `Rnd [concl]

  (* -------------------------------------------------------------------- *)
  let wp_equiv_disj_rnd_r side tc =
    let env = FApi.tc1_env tc in
    let es  = tc1_as_equivS tc in
    let ml, mr = fst es.es_ml, fst es.es_mr in
    let m, mo, s =
      match side with
      | `Left  -> es.es_ml, fst es.es_mr, es.es_sl
      | `Right -> es.es_mr, fst es.es_ml, es.es_sr
    in
    let subst_form_lv_side = sideif side subst_form_lv_left subst_form_lv_right in
    let ss_inv_generalize_other =
      sideif side ss_inv_generalize_right ss_inv_generalize_left in
    (* FIXME: exception when not rnds found *)
    let (lv, distr), s = tc1_last_rnd tc s in
    let ty_distr = proj_distr_ty env (e_ty distr) in

    let x_id = EcIdent.create (symbol_of_lv lv) in
    let x    = {ml; mr; inv=f_local x_id ty_distr} in

    let distr = EcFol.ss_inv_of_expr (EcMemory.memory m) distr in
    let distr = ss_inv_generalize_other distr mo in
    let post  = subst_form_lv_side env lv x (es_po es) in
    let post  = map_ts_inv2 f_imp (map_ts_inv2 f_in_supp x distr) post in
    let post  = map_ts_inv1 (f_forall_simpl [(x_id,GTty ty_distr)]) post in
    let post  = map_ts_inv2 f_anda (map_ts_inv1 (f_lossless ty_distr) distr) post in
    let concl =
      match side with
      | `Left  -> f_equivS (snd es.es_ml) (snd es.es_mr) (es_pr es) s es.es_sr post
      | `Right -> f_equivS (snd es.es_ml) (snd es.es_mr) (es_pr es) es.es_sl s post
    in
    FApi.xmutate1 tc `Rnd [concl]

  (* -------------------------------------------------------------------- *)
  let wp_equiv_rnd_r bij tc =
    let env = FApi.tc1_env tc in
    let es = tc1_as_equivS tc in
    let ml, mr = fst es.es_ml, fst es.es_mr in
    let (lvL, muL), sl' = tc1_last_rnd tc es.es_sl in
    let (lvR, muR), sr' = tc1_last_rnd tc es.es_sr in
    let tyL = proj_distr_ty env (e_ty muL) in
    let tyR = proj_distr_ty env (e_ty muR) in
    let xL_id = EcIdent.create (symbol_of_lv lvL ^ "L")
    and xR_id = EcIdent.create (symbol_of_lv lvR ^ "R") in
    let xL  = {ml;mr;inv=f_local xL_id tyL} in
    let xR  = {ml;mr;inv=f_local xR_id tyR} in
    let muL = EcFol.ss_inv_of_expr ml muL in
    let muR = EcFol.ss_inv_of_expr mr muR in

    let tf, tfinv =
      match bij with
      | Some (f, finv) -> (f tyL tyR, finv tyR tyL)
      | None ->
        if not (EcReduction.EqTest.for_type env tyL tyR) then
          tc_error !!tc "%s, %s"
            "support are not compatible"
            "an explicit bijection is required";
        ({ml;mr;inv=EcFol.f_identity ~name:"z" tyL},
         {ml;mr;inv=EcFol.f_identity ~name:"z" tyR})
    in

    (*     (∀ x₂, x₂ ∈ ℑ(D₂) ⇒ x₂ = f(f⁻¹(x₂))
     *  && (∀ x₂, x₂ ∈ ℑ(D₂) ⇒ μ(x₂, D₂) = μ(f⁻¹(x₂), D₁))
     *  && (∀ x₁, x₁ ∈ ℑ(D₁) ⇒ f(x₁) ∈ ℑ(D₂) && x₁ = f⁻¹(f(x₁)) && φ(x₁, f(x₁)))
     *)

    let f_app_simpl' ty f t = f_app_simpl f [t] ty in
    let f    t = map_ts_inv2 (f_app_simpl' tyR) tf t in
    let finv t = map_ts_inv2 (f_app_simpl' tyL) tfinv t in

    let post = subst_form_lv_left env lvL xL  (es_po es) in
    let post = subst_form_lv_right env lvR (f xL) post in

    let muL = ss_inv_generalize_right muL mr in
    let muR = ss_inv_generalize_left muR ml in

    let cond_fbij      = map_ts_inv2 f_eq xL (finv (f xL)) in
    let cond_fbij_inv  = map_ts_inv2 f_eq xR (f (finv xR)) in

    let cond1 = map_ts_inv2 f_imp (map_ts_inv2 f_in_supp xR muR) cond_fbij_inv in
    let cond2 = map_ts_inv2 f_imp (map_ts_inv2 f_in_supp xR muR) (map_ts_inv2 f_eq (map_ts_inv2 f_mu_x muR xR) (map_ts_inv2 f_mu_x muL (finv xR))) in
    let cond3 = map_ts_inv f_andas [map_ts_inv2 f_in_supp (f xL) muR; cond_fbij; post] in
    let cond3 = map_ts_inv2 f_imp (map_ts_inv2 f_in_supp xL muL) cond3 in

    let concl = map_ts_inv f_andas
      [map_ts_inv1 (f_forall_simpl [(xR_id, GTty tyR)]) cond1;
       map_ts_inv1 (f_forall_simpl [(xR_id, GTty tyR)]) cond2;
       map_ts_inv1 (f_forall_simpl [(xL_id, GTty tyL)]) cond3] in

    let concl = f_equivS (snd es.es_ml) (snd es.es_mr) (es_pr es) sl' sr' concl in

    FApi.xmutate1 tc `Rnd [concl]

  (* -------------------------------------------------------------------- *)
  let t_bdhoare_rnd_r tac_info tc =
    let env = FApi.tc1_env tc in
    let bhs = tc1_as_bdhoareS tc in
    let (lv,distr),s = tc1_last_rnd tc bhs.bhs_s in
    let ty_distr = proj_distr_ty env (e_ty distr) in
    let distr = EcFol.ss_inv_of_expr (EcMemory.memory bhs.bhs_m) distr in
    let m = fst bhs.bhs_m in
    let mk_event_cond event =
      let v_id = EcIdent.create "v" in
      let v = {m; inv=f_local v_id ty_distr} in
      let post_v = subst_form_lv env lv v (bhs_po bhs) in
      let f_app' fl = f_app (List.hd fl) (List.tl fl) tbool in
      let event_v = map_ss_inv f_app' [event ;v] in
      let v_in_supp = map_ss_inv2 f_in_supp v distr in
      map_ss_inv1 (f_forall_simpl [v_id,GTty ty_distr])
        begin
          let f_imps_simpl' fl = f_imps_simpl  (List.tl fl) (List.hd fl) in
          match bhs.bhs_cmp with
          | FHle -> map_ss_inv f_imps_simpl' [event_v; v_in_supp;post_v]
          | FHge -> map_ss_inv f_imps_simpl' [post_v; v_in_supp;event_v]
          | FHeq -> map_ss_inv2 f_imp_simpl v_in_supp (map_ss_inv2 f_iff_simpl event_v post_v)
        end
    in
    let f_cmp = match bhs.bhs_cmp with
      | FHle -> f_real_le
      | FHge -> fun x y -> f_real_le y x
      | FHeq -> f_eq
    in
    let is_post_indep =
      let fv = EcPV.PV.fv env (bhs_po bhs).m (bhs_po bhs).inv in
      match lv with
      | LvVar (x,_) -> not (EcPV.PV.mem_pv env x fv)
      | LvTuple pvs ->
        List.for_all (fun (x,_) -> not (EcPV.PV.mem_pv env x fv)) pvs
    in
    let is_bd_indep =
      let fv_bd = PV.fv env (bhs_bd bhs).m (bhs_bd bhs).inv in
      let modif_s = s_write env s in
      PV.indep env modif_s fv_bd
    in
    let mk_event ?(simpl=true) ty =
      let x = EcIdent.create "x" in
      if is_post_indep && simpl then f_predT ty
      else match lv with
           | LvVar (pv,_) ->
             f_lambda [x,GTty ty]
               (EcPV.PVM.subst1 env pv m (f_local x ty) (bhs_po bhs).inv)
           | _ -> tc_error !!tc "cannot infer a valid event, it must be provided"
    in
    let bound,pre_bound,binders =
      if is_bd_indep then
        bhs_bd bhs, {m;inv=f_true}, []
      else
        let bd_id = EcIdent.create "bd" in
        let bd = {m;inv=f_local bd_id treal} in
        bd, map_ss_inv2 f_eq (bhs_bd bhs) bd, [(bd_id,GTty treal)]
    in
    let subgoals = match tac_info, bhs.bhs_cmp with
      | PNoRndParams, FHle ->
        if is_post_indep then
          (* event is true *)
          let concl = f_bdHoareS (snd bhs.bhs_m) 
            (bhs_pr bhs) s (bhs_po bhs) bhs.bhs_cmp (bhs_bd bhs) in
          [concl]
        else
          let event = {m; inv=mk_event ty_distr} in
          let bounded_distr = map_ss_inv2 f_real_le (map_ss_inv2 (f_mu env) distr event) bound in
          let pre = map_ss_inv2 f_and (bhs_pr bhs) pre_bound in
          let post = map_ss_inv2 f_anda bounded_distr (mk_event_cond event) in
          let concl = f_hoareS (snd bhs.bhs_m) pre s post in
          let concl = f_forall_simpl binders concl in
          [concl]
      | PNoRndParams, _ ->
        if is_post_indep then
          (* event is true *)
          let event = {m;inv=mk_event ty_distr} in
          let f_r1 = {m;inv=f_r1} in
          let bounded_distr = map_ss_inv2 f_eq (map_ss_inv2 (f_mu env) distr event) f_r1 in
          let post = map_ss_inv2 f_and (bhs_po bhs) bounded_distr in
          let concl = f_bdHoareS (snd bhs.bhs_m) (bhs_pr bhs) s post bhs.bhs_cmp (bhs_bd bhs) in
          [concl]
        else
          let event = {m;inv=mk_event ty_distr} in
          let bounded_distr = map_ss_inv2 f_cmp (map_ss_inv2 (f_mu env) distr event) bound in
          let pre = map_ss_inv2 f_and (bhs_pr bhs) pre_bound in
          let post = map_ss_inv2 f_anda bounded_distr (mk_event_cond event) in
          let concl = f_bdHoareS (snd bhs.bhs_m) pre s post bhs.bhs_cmp {m;inv=f_r1} in
          let concl = f_forall_simpl binders concl in
          [concl]
      | PSingleRndParam event, FHle ->
          let event = event ty_distr in
          let bounded_distr = map_ss_inv2 f_real_le (map_ss_inv2 (f_mu env) distr event) bound in
          let pre = map_ss_inv2 f_and (bhs_pr bhs) pre_bound in
          let post = map_ss_inv2 f_anda bounded_distr (mk_event_cond event) in
          let concl = f_hoareS (snd bhs.bhs_m) pre s post in
          let concl = f_forall_simpl binders concl in
          [concl]
      | PSingleRndParam event, _ ->
          let event = event ty_distr in
          let bounded_distr = map_ss_inv2 f_cmp (map_ss_inv2 (f_mu env) distr event) bound in
          let pre = map_ss_inv2 f_and (bhs_pr bhs) pre_bound in
          let post = map_ss_inv2 f_anda bounded_distr (mk_event_cond event) in
          let concl = f_bdHoareS (snd bhs.bhs_m) pre s post FHeq {m;inv=f_r1} in
          let concl = f_forall_simpl binders concl in
          [concl]
      | PMultRndParams ((phi,d1,d2,d3,d4),event), _ ->
        let event = match event ty_distr with
          | None -> {m;inv=mk_event ~simpl:false ty_distr} | Some event -> event
        in
        let bd_sgoal = map_ss_inv2 f_cmp (map_ss_inv2 f_real_add (map_ss_inv2 f_real_mul d1 d2) (map_ss_inv2 f_real_mul d3 d4)) (bhs_bd bhs) in
        let bd_sgoal = f_forall_mems_ss_inv (bhs.bhs_m) bd_sgoal in
        let sgoal1 = f_bdHoareS (snd bhs.bhs_m) (bhs_pr bhs) s phi bhs.bhs_cmp d1 in
        let sgoal2 =
          let bounded_distr = map_ss_inv2 f_cmp (map_ss_inv2 (f_mu env) distr event) d2 in
          let post = map_ss_inv2 f_anda bounded_distr (mk_event_cond event) in
          f_forall_mems_ss_inv (bhs.bhs_m) (map_ss_inv2 f_imp phi post)
        in
        let sgoal3 = f_bdHoareS (snd bhs.bhs_m) (bhs_pr bhs) s (map_ss_inv1 f_not phi) bhs.bhs_cmp d3 in
        let sgoal4 =
          let bounded_distr = map_ss_inv2 f_cmp (map_ss_inv2 (f_mu env) distr event) d4 in
          let post = map_ss_inv2 f_anda bounded_distr (mk_event_cond event) in
          f_forall_mems_ss_inv bhs.bhs_m (map_ss_inv2 f_imp (map_ss_inv1 f_not phi) post) in
        let sgoal5 =
          let f_inbound x = 
            let f_r1, f_r0 = {m;inv=f_r1}, {m;inv=f_r0} in
            map_ss_inv2 f_anda (map_ss_inv2 f_real_le f_r0 x) (map_ss_inv2 f_real_le x f_r1) in
          map_ss_inv f_ands (List.map f_inbound [d1; d2; d3; d4])
        in
        let sgoal5 = f_forall_mems_ss_inv (bhs.bhs_m) sgoal5 in
        [bd_sgoal;sgoal1;sgoal2;sgoal3;sgoal4;sgoal5]

      | _, _ -> tc_error !!tc "invalid arguments"
    in

    FApi.xmutate1 tc `Rnd subgoals

  (* -------------------------------------------------------------------- *)
  let semrnd tc mem used (s : instr list) : EcMemory.memenv * instr list =
    let error () = tc_error !!tc "semrnd" in

    let env = FApi.tc1_env tc in
    let wr, gwr = PV.elements (is_write env s) in
    let wr =
      match used with
      | None -> wr
      | Some used -> List.filter (fun (pv, _) -> PV.mem_pv env pv used) wr in

    if not (List.is_empty gwr) then
      error ();

    let open EcPV in

    let wr =
      let add (m, idx) pv =
        if   is_some (PVMap.find pv m)
        then (m, idx)
        else (PVMap.add pv idx m, idx+1) in

      let m, idx =
        List.fold_left (fun (m, idx) { i_node = i } ->
          match i with
          | Sasgn (lv, _) | Srnd (lv, _) ->
             List.fold_left add (m, idx) (lv_to_list lv)
          | _ -> (m, idx)
        )
        (PVMap.create env, 0) s in

      let m, _ =
        List.fold_left
          (fun (m, idx) (pv, _) -> add (m, idx) pv)
          (m, idx)
          wr in

      List.sort
        (fun (pv1, _) (pv2, _) ->
          compare (PVMap.find pv1 m) (PVMap.find pv2 m))
        wr in

    let rec do1 (m: memory) (subst : PVM.subst) (s : instr list) =
      match s with
      | [] ->
         let tuple =
           List.map (fun (pv, _) ->
             PVM.find env pv m subst) wr in
         {m;inv=f_dunit (f_tuple tuple)}

      | { i_node = Sasgn (lv, e) } :: s ->
         let e = ss_inv_of_expr m e in
         let e = map_ss_inv1 (PVM.subst env subst) e in
         let subst =
           match lv with
           | LvVar (pv, _) ->
              PVM.add env pv m e.inv subst
           | LvTuple pvs ->
              List.fold_lefti (fun subst i (pv, ty) ->
                PVM.add env pv m (f_proj e.inv i ty) subst
              ) subst pvs
         in
         do1 m subst s

      | { i_node = Srnd (lv, d) } :: s ->
         let d = ss_inv_of_expr m d in
         let d = map_ss_inv1 (PVM.subst env subst) d in
         let x = EcIdent.create (name_of_lv lv) in
         let subst, xty =
           match lv with
           | LvVar (pv, ty) ->
              let x = f_local x ty in
              (PVM.add env pv m x subst, ty)
           | LvTuple pvs ->
              let ty = ttuple (List.snd pvs) in
              let x = f_local x ty in
              let subst =
                List.fold_lefti (fun subst i (pv, ty) ->
                  PVM.add env pv m (f_proj x i ty) subst
                ) subst pvs in
              (subst, ty)
         in
         let body = do1 m subst s in

         map_ss_inv2
         (f_dlet_simpl
           xty
           (ttuple (List.snd wr)))
           d
           (map_ss_inv1 (f_lambda [(x, GTty xty)]) body)

      | _ :: _ ->
         error ()

    in

    let mhr = EcIdent.create "&hr" in
    let distr = do1 mhr PVM.empty s in
    let distr = expr_of_ss_inv distr in

    match lv_of_list wr with
    | None ->
       let x =  { ov_name = Some "x"; ov_type = tunit; } in
       let mem, x = EcMemory.bind_fresh x mem in
       let x, xty = pv_loc (oget x.ov_name), x.ov_type in
       (mem, [i_rnd (LvVar (x, xty), distr)])
    | Some wr ->
       (mem, [i_rnd (wr, distr)])

  (* -------------------------------------------------------------------- *)
  let t_hoare_rndsem_r reduce pos tc =
    let env = FApi.tc1_env tc in
    let hs = tc1_as_hoareS tc in
    let s1, s2 = o_split env (Some pos) hs.hs_s in
    let fv =
      if reduce then
        Some (PV.fv (FApi.tc1_env tc) (fst hs.hs_m) (hs_po hs).inv)
      else None in
    let (_, mt), s2 = semrnd tc hs.hs_m fv s2 in
    let concl = f_hoareS mt (hs_pr hs) (stmt (s1 @ s2)) (hs_po hs) in
    FApi.xmutate1 tc (`RndSem pos) [concl]

 (* -------------------------------------------------------------------- *)
  let t_bdhoare_rndsem_r reduce pos tc =
    let env = FApi.tc1_env tc in
    let bhs = tc1_as_bdhoareS tc in
    let s1, s2 = o_split env (Some pos) bhs.bhs_s in
    let fv =
      if reduce then
        Some (PV.fv (FApi.tc1_env tc) (fst bhs.bhs_m) (bhs_po bhs).inv)
      else None in
    let (_,mt), s2 = semrnd tc bhs.bhs_m fv s2 in
    let concl = f_bdHoareS mt (bhs_pr bhs) (stmt (s1 @ s2)) (bhs_po bhs) bhs.bhs_cmp (bhs_bd bhs) in
    FApi.xmutate1 tc (`RndSem pos) [concl]

 (* -------------------------------------------------------------------- *)
  let t_equiv_rndsem_r reduce side pos tc =
    let env = FApi.tc1_env tc in
    let es = tc1_as_equivS tc in
    let s, m =
      match side with
      | `Left  -> es.es_sl, es.es_ml
      | `Right -> es.es_sr, es.es_mr in
    let s1, s2 = o_split env (Some pos) s in
    let fv =
      if reduce then
        Some (PV.fv (FApi.tc1_env tc) (fst m) (es_po es).inv)
      else None in
    let (_,mt), s2 = semrnd tc m fv s2 in
    let s = stmt (s1 @ s2) in
    let concl =
      match side with
      | `Left  -> f_equivS mt (snd es.es_mr) (es_pr es) s es.es_sr (es_po es)
      | `Right -> f_equivS (snd es.es_ml) mt (es_pr es) es.es_sl s (es_po es) in
    FApi.xmutate1 tc (`RndSem pos) [concl]

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
  let (c1, c2) = map_ts_inv_destr2 destr_and (es_po es) in
  let newc1 = EcSubst.f_forall_mems_ts_inv es.es_ml es.es_mr c1 in

  let subtc = tc in
  let subtc, hdc1 = solve 2 newc1 subtc in

  match hdc1 with
  | None -> tc
  | Some hd ->
    let po = c2 in
    FApi.t_onalli (function
    | 0 -> fun tc -> EcLowGoal.t_trivial tc
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
      (EcPhlConseq.t_equivS_conseq (es_pr es) po)
      subtc)

(* -------------------------------------------------------------------- *)
let wp_equiv_rnd_r bij tc =
  let tc = Core.wp_equiv_rnd_r bij tc in
  let es = tc1_as_equivS (FApi.as_tcenv1 tc) in

  let c1, c2, c3 = map_ts_inv_destr3 destr_and3 (es_po es) in
  let (x, xty, _) = destr_forall1 c3.inv in
  let c3 = map_ts_inv1 (fun c3 -> let (_,_,d) = destr_forall1 c3 in d) c3 in
  let (ind, c3) = map_ts_inv_destr2 destr_imp c3 in
  let (c3, c4) = map_ts_inv_destr2 destr_and c3 in
  let newc2 = EcSubst.f_forall_mems_ts_inv es.es_ml es.es_mr c2 in
  let newc3 = EcSubst.f_forall_mems_ts_inv es.es_ml es.es_mr
                (map_ts_inv1 (f_forall [x, xty]) (map_ts_inv2 f_imp ind c3)) in

  let subtc = tc in
  let subtc, hdc2 = solve 4 newc2 subtc in
  let subtc, hdc3 = solve 4 newc3 subtc in

  let po =
    match hdc2, hdc3 with
    | None  , None   -> None
    | Some _, Some _ -> 
      Some (map_ts_inv2 f_anda c1 (map_ts_inv1 (f_forall [x, xty]) (map_ts_inv2 f_imp ind c4)))
    | Some _, None   -> 
      Some (map_ts_inv2 f_anda c1 (map_ts_inv1 (f_forall [x, xty]) (map_ts_inv2 f_imp ind (map_ts_inv2 f_anda c3 c4))))
    | None  , Some _ -> 
      Some (map_ts_inv f_andas [c1; c2; map_ts_inv1 (f_forall [x, xty]) (map_ts_inv2 f_imp ind c4)])
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
    | 0 -> fun tc -> EcLowGoal.t_trivial tc
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
      (EcPhlConseq.t_equivS_conseq (es_pr es) po)
      subtc)

(* -------------------------------------------------------------------- *)
let t_equiv_rnd_r side pos bij_info tc =
  match side, pos with
  | Some side, None ->
     wp_equiv_disj_rnd_r side tc
  | None, _ -> begin
      let pos =
        match pos with
        | None -> None
        | Some (Single i) -> Some (i, i)
        | Some (Double (il, ir)) -> Some (il, ir) in

      let tc =
        match pos with
        | None ->
           t_id tc
        | Some ((bl, il), (br, ir)) ->
           FApi.t_seq
             (Core.t_equiv_rndsem_r bl `Left il)
             (Core.t_equiv_rndsem_r br `Right ir)
             tc in

      let bij =
        match bij_info with
        | Some f, Some finv ->  Some (f, finv)
        | Some bij, None | None, Some bij -> Some (bij, bij)
        | None, None -> None
      in
      FApi.t_first (wp_equiv_rnd_r bij) tc
    end

  | _ ->
     tc_error !!tc "invalid argument"

(* -------------------------------------------------------------------- *)
let wp_equiv_disj_rnd = FApi.t_low1 "wp-equiv-disj-rnd" wp_equiv_disj_rnd_r
let wp_equiv_rnd      = FApi.t_low1 "wp-equiv-rnd" wp_equiv_rnd_r

(* -------------------------------------------------------------------- *)
let t_hoare_rnd   = FApi.t_low0 "hoare-rnd"   Core.t_hoare_rnd_r
let t_ehoare_rnd  = FApi.t_low0 "ehoare-rnd"   Core.t_ehoare_rnd_r
let t_bdhoare_rnd = FApi.t_low1 "bdhoare-rnd" Core.t_bdhoare_rnd_r

let t_equiv_rnd ?pos side bij_info =
  (FApi.t_low3 "equiv-rnd" t_equiv_rnd_r) side pos bij_info

(* -------------------------------------------------------------------- *)
let process_rnd side pos tac_info tc =
  let concl = FApi.tc1_goal tc in

  match side, pos, tac_info with
  | None, None, PNoRndParams when is_hoareS concl ->
      t_hoare_rnd tc

  | None, None, PNoRndParams when is_eHoareS concl ->
      t_ehoare_rnd tc

  | None, None, _ when is_bdHoareS concl ->
    let tac_info =
      match tac_info with
      | PNoRndParams ->
          PNoRndParams

      | PSingleRndParam fp ->
          PSingleRndParam
            (fun t -> snd (TTC.tc1_process_Xhl_form tc (tfun t tbool) fp))

      | PMultRndParams ((phi, d1, d2, d3, d4), p) ->
          let p t = p |> omap (fun p -> snd (TTC.tc1_process_Xhl_form tc (tfun t tbool) p)) in
          let _, phi = TTC.tc1_process_Xhl_form tc tbool phi in
          let _, d1  = TTC.tc1_process_Xhl_form tc treal d1 in
          let _, d2  = TTC.tc1_process_Xhl_form tc treal d2 in
          let _, d3  = TTC.tc1_process_Xhl_form tc treal d3 in
          let _, d4  = TTC.tc1_process_Xhl_form tc treal d4 in
          PMultRndParams ((phi, d1, d2, d3, d4), p)

      | _ -> tc_error !!tc "invalid arguments"
    in
      t_bdhoare_rnd tac_info tc

  | _, _, _ when is_equivS concl ->
    let process_form f ty1 ty2 =
      TTC.tc1_process_prhl_form tc (tfun ty1 ty2) f in

    let bij_info =
      match tac_info with
      | PNoRndParams -> None, None
      | PSingleRndParam f -> Some (process_form f), None
      | PTwoRndParams (f, finv) -> Some (process_form f), Some (process_form finv)
      | _ -> tc_error !!tc "invalid arguments"
    in

    let pos = pos |> Option.map (function
      | Single (b, p) ->
          let p =
            if Option.is_some side then
              EcProofTyping.tc1_process_codepos1 tc (side, p)
            else EcTyping.trans_codepos1 (FApi.tc1_env tc) p
          in Single (b, p)
      | Double ((b1, p1), (b2, p2)) ->
          let p1 = EcProofTyping.tc1_process_codepos1 tc (Some `Left , p1) in
          let p2 = EcProofTyping.tc1_process_codepos1 tc (Some `Right, p2) in
          Double ((b1, p1), (b2, p2))
    )
    in
    
    t_equiv_rnd side ?pos bij_info tc

  | _ -> tc_error !!tc "invalid arguments"

(* -------------------------------------------------------------------- *)
let t_hoare_rndsem   = FApi.t_low2 "hoare-rndsem"   Core.t_hoare_rndsem_r
let t_bdhoare_rndsem = FApi.t_low2 "bdhoare-rndsem" Core.t_bdhoare_rndsem_r
let t_equiv_rndsem   = FApi.t_low3 "equiv-rndsem"   Core.t_equiv_rndsem_r

(* -------------------------------------------------------------------- *)
let process_rndsem ~reduce side pos tc =
  let concl = FApi.tc1_goal tc in
  let pos = EcProofTyping.tc1_process_codepos1 tc (side, pos) in

  match side with
  | None when is_hoareS concl ->
     t_hoare_rndsem reduce pos tc
  | None when is_bdHoareS concl ->
     t_bdhoare_rndsem reduce pos tc
  | Some side when is_equivS concl ->
     t_equiv_rndsem reduce side pos tc
  | _ -> tc_error !!tc "invalid arguments"
