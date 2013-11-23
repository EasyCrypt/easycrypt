(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcTypes
open EcModules
open EcFol
open EcBaseLogic
open EcLogic
open EcPV
open EcCorePhl
open EcCoreHiPhl

(* -------------------------------------------------------------------- *)
class rn_hl_hoare_rnd =
object
  inherit xrule "[hl] hoare-rnd"
end

(* -------------------------------------------------------------------- *)
type hl_infos_t = (form, form, form) rnd_tac_info

class rn_hl_equiv_rnd infos =
object
  inherit xrule "[hl] equiv-rnd"

  method infos : hl_infos_t = infos
end

(* -------------------------------------------------------------------- *)
type bhl_infos_t = (form, ty -> form option, ty -> form) rnd_tac_info

class rn_hl_bhl_rnd infos =
object
  inherit xrule "[bhl] hoare-rnd"

  method infos : bhl_infos_t = infos
end

(* -------------------------------------------------------------------- *)
let rn_hl_hoare_rnd =
  RN_xtd (new rn_hl_hoare_rnd)

let rn_hl_equiv_rnd infos =
  RN_xtd (new rn_hl_equiv_rnd infos :> xrule)

let rn_bhl_rnd infos =
  RN_xtd (new rn_hl_bhl_rnd infos :> xrule)

(* -------------------------------------------------------------------- *)
let t_hoare_rnd g =
  let env,_,concl = get_goal_e g in
  let hs = t_as_hoareS concl in
  let (lv,distr),s= s_last_rnd "rnd" hs.hs_s in
  (* FIXME: exception when not rnds found *)
  let ty_distr = proj_distr_ty (e_ty distr) in
  let x_id = EcIdent.create (symbol_of_lv lv) in
  let x = f_local x_id ty_distr in
  let distr = EcFol.form_of_expr (EcMemory.memory hs.hs_m) distr in
  let post = subst_form_lv env (EcMemory.memory hs.hs_m) lv x hs.hs_po in
  let post = f_imp (f_in_supp x distr) post in
  let post = f_forall_simpl [(x_id,GTty ty_distr)] post in
  let concl = f_hoareS_r {hs with hs_s=s; hs_po=post} in
  prove_goal_by [concl] rn_hl_hoare_rnd g

(* -------------------------------------------------------------------- *)
let wp_equiv_disj_rnd side g =
  let env,_,concl = get_goal_e g in
  let es = t_as_equivS concl in
  let m,s =
    if side then es.es_ml, es.es_sl
    else         es.es_mr, es.es_sr
  in
  let (lv,distr),s= s_last_rnd "rnd" s in

  (* FIXME: exception when not rnds found *)
  let ty_distr = proj_distr_ty (e_ty distr) in
  let x_id = EcIdent.create (symbol_of_lv lv) in
  let x = f_local x_id ty_distr in
  let distr = EcFol.form_of_expr (EcMemory.memory m) distr in
  let post = subst_form_lv env (EcMemory.memory m) lv x es.es_po in
  let post = f_imp (f_in_supp x distr) post in
  let post = f_forall_simpl [(x_id,GTty ty_distr)] post in
  let post = f_anda (f_eq (f_weight ty_distr distr) f_r1) post in
  let concl =
    if side then f_equivS_r {es with es_sl=s; es_po=post}
    else  f_equivS_r {es with es_sr=s; es_po=post}
  in
  prove_goal_by [concl] rn_hl_hoare_rnd g

(* -------------------------------------------------------------------- *)
let wp_equiv_rnd (f,finv) g =
  let env,_,concl = get_goal_e g in
  let es = t_as_equivS concl in
  let (lvL,muL),(lvR,muR),sl',sr'= s_last_rnds "rnd" es.es_sl es.es_sr in
  (* FIXME: exception when not rnds found *)
  let tyL = proj_distr_ty (e_ty muL) in
  let tyR = proj_distr_ty (e_ty muR) in
  let x_id = EcIdent.create (symbol_of_lv lvL ^ "L")
  and y_id = EcIdent.create (symbol_of_lv lvR ^ "R") in
  let x = f_local x_id tyL in
  let y = f_local y_id tyR in
  let muL = EcFol.form_of_expr (EcMemory.memory es.es_ml) muL in
  let muR = EcFol.form_of_expr (EcMemory.memory es.es_mr) muR in
  (* *)
  let tf = f tyL tyR in
  let tfinv = finv tyR tyL in
  let f t = f_app tf  [t] tyR in
  let finv t = f_app tfinv [t] tyL in
  let supp_cond1 =  f_eq (f_mu_x muL x) (f_mu_x muR (f x)) in
  let supp_cond2 =  f_in_supp (finv y) muL in
  let inv_cond1 =   f_eq (finv (f x)) x in
  let inv_cond2 =   f_eq (f (finv y)) y in
  let post = subst_form_lv env (EcMemory.memory es.es_ml) lvL x es.es_po in
  let post = subst_form_lv env (EcMemory.memory es.es_mr) lvR (f x) post in
  let post = f_andas [supp_cond1; supp_cond2; inv_cond1; inv_cond2; post] in
  let post = f_imp (f_in_supp y muR) post in
  let post = f_imp (f_in_supp x muL) post in
  let post = f_forall_simpl [(x_id,GTty tyL);(y_id,GTty tyR)] post in
  let concl = f_equivS_r {es with es_sl=sl'; es_sr=sr'; es_po=post} in
  prove_goal_by [concl] (rn_hl_equiv_rnd (PTwoRndParams (tf, tfinv))) g

(* -------------------------------------------------------------------- *)
let t_equiv_rnd side bij_info =
  match side with
  | Some side -> wp_equiv_disj_rnd side
  | None  ->
    let f,finv =  match bij_info with
      | Some f, Some finv ->  f, finv
      | Some bij, None | None, Some bij -> bij, bij
      | None, None ->
        let z_id = EcIdent.create "z" in
        let z = f_local z_id in
        let bij = fun tyL tyR -> f_lambda [z_id,GTty tyR] (z tyL) in
          (* TODO Cezar : Can it be not well typed: normally tyL and tyR should
             be equal.
             I propose to replace tyL by tyR
          *)
        bij, bij
    in wp_equiv_rnd (f, finv)

(* -------------------------------------------------------------------- *)
let t_bd_hoare_rnd tac_info g =
  let env,_,concl = get_goal_e g in
  let bhs = t_as_bdHoareS concl in
  let (lv,distr),s = s_last_rnd "bd_hoare_rnd" bhs.bhs_s in
  let ty_distr = proj_distr_ty (e_ty distr) in
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
      | LvMap(_, x,_,_) -> not (EcPV.PV.mem_pv env x fv)
  in
  let is_bd_indep =
    let fv_bd = PV.fv env mhr bhs.bhs_bd in
    let modif_s = s_write env s in
    PV.indep env modif_s fv_bd
  in
  let mk_event ?(simpl=true) ty =
    let x = EcIdent.create "x" in
    if is_post_indep && simpl then f_lambda [x,GTty ty] f_true
    else match lv with
      | LvVar (pv,_) ->
        f_lambda [x,GTty ty]
          (EcPV.PVM.subst1 env pv m (f_local x ty) bhs.bhs_po)
      | _ -> tacuerror "Cannot infer a valid event, it must be provided"
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
        let bounded_distr = f_real_le (f_mu distr event) bound in
        let pre = f_and bhs.bhs_pr pre_bound in
        let post = f_anda bounded_distr (mk_event_cond event) in
        let concl = f_hoareS bhs.bhs_m pre s post in
        let concl = f_forall_simpl binders concl in
        [concl]
    | PNoRndParams, _ ->
      if is_post_indep then
        (* event is true *)
        let event = mk_event ty_distr in
        let bounded_distr = f_eq (f_mu distr event) f_r1 in
        let concl = f_bdHoareS_r
          {bhs with bhs_s=s; bhs_po=f_and bhs.bhs_po bounded_distr} in
        [concl]
      else
        let event = mk_event ty_distr in
        let bounded_distr = f_cmp (f_mu distr event) bound in
        let pre = f_and bhs.bhs_pr pre_bound in
        let post = f_anda bounded_distr (mk_event_cond event) in
        let concl = f_bdHoareS_r {bhs with bhs_s=s; bhs_pr=pre; bhs_po=post; bhs_bd=f_r1} in
        let concl = f_forall_simpl binders concl in
        [concl]
    | PSingleRndParam event, FHle ->
        let event = event ty_distr in
        let bounded_distr = f_real_le (f_mu distr event) bound in
        let pre = f_and bhs.bhs_pr pre_bound in
        let post = f_anda bounded_distr (mk_event_cond event) in
        let concl = f_hoareS bhs.bhs_m pre s post in
        let concl = f_forall_simpl binders concl in
        [concl]
    | PSingleRndParam event, _ ->
        let event = event ty_distr in
        let bounded_distr = f_cmp (f_mu distr event) bound in
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
        let bounded_distr = f_cmp (f_mu distr event) d2 in
        let post = f_anda bounded_distr (mk_event_cond event) in
        f_forall_mems [bhs.bhs_m] (f_imp phi post)
      in
      let sgoal3 = f_bdHoareS_r {bhs with bhs_s=s; bhs_po=f_not phi; bhs_bd=d3} in
      let sgoal4 =
        let bounded_distr = f_cmp (f_mu distr event) d4 in
        let post = f_anda bounded_distr (mk_event_cond event) in
        f_forall_mems [bhs.bhs_m] (f_imp (f_not phi) post)
      in
      [bd_sgoal;sgoal1;sgoal2;sgoal3;sgoal4]
    | _, _ -> tacuerror "wrong tactic arguments"
in
prove_goal_by subgoals (rn_bhl_rnd tac_info) g

(* -------------------------------------------------------------------- *)
let process_rnd side tac_info g =
  let concl = get_concl g in

  match side, tac_info with
  | None, PNoRndParams when is_hoareS concl ->
      t_hoare_rnd g

  | None, _ when is_bdHoareS concl ->
    let tac_info =
      match tac_info with
      | PNoRndParams ->
          PNoRndParams

      | PSingleRndParam p ->
          PSingleRndParam (fun t -> process_phl_form (tfun t tbool) g p)

      | PMultRndParams ((phi,d1,d2,d3,d4),p) ->
          let p t = p |> omap (process_phl_form (tfun t tbool) g) in
          let phi = process_phl_form tbool g phi in
          let d1 = process_phl_form treal g d1 in
          let d2 = process_phl_form treal g d2 in
          let d3 = process_phl_form treal g d3 in
          let d4 = process_phl_form treal g d4 in
            PMultRndParams ((phi, d1, d2, d3, d4), p)

      | _ -> tacuerror "wrong tactic arguments"
    in
      t_bd_hoare_rnd tac_info g

  | _ when is_equivS concl ->
    let process_form f ty1 ty2 = process_prhl_form (tfun ty1 ty2) g f in
    let bij_info =
      match tac_info with
      | PNoRndParams -> None, None
      | PSingleRndParam f -> Some (process_form f), None
      | PTwoRndParams (f, finv) -> Some (process_form f), Some (process_form finv)
      | _ -> tacuerror "wrong tactic arguments"
    in
      t_equiv_rnd side bij_info g

  | _ -> cannot_apply "rnd" "unexpected instruction or wrong arguments"
