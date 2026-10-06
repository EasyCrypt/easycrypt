(* -------------------------------------------------------------------- *)
open EcParsetree
open EcTypes
open EcModules
open EcFol
open EcAst
open EcEnv
open EcPV
open EcSubst

open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal

module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
(* Parameters of the bdhoare [rnd] rule as supplied by the caller: high level,
   the event and the bounds may depend on the (not yet known) type of the
   sampled values. *)
type bdhoare_rnd_rule = {
  brr_info : (ss_inv, ty -> ss_inv option, ty -> ss_inv) rnd_tac_info;
}

(* Low-level parameters recorded in the proof-node: the event and the bounds
   instantiated at the type of the sampled values. *)
type bdhoare_rnd_split = {
  brs_phi   : ss_inv;          (* condition splitting the prefix runs *)
  brs_d1    : ss_inv;          (* bound for the prefix, under phi *)
  brs_d2    : ss_inv;          (* bound for the sampling, under phi *)
  brs_d3    : ss_inv;          (* bound for the prefix, under !phi *)
  brs_d4    : ss_inv;          (* bound for the sampling, under !phi *)
  brs_event : ss_inv option;   (* event (inferred when absent) *)
}

type bdhoare_rnd_node =
  | BRndInfer                      (* no argument: the event is inferred *)
  | BRndEvent of ss_inv            (* the event *)
  | BRndSplit of bdhoare_rnd_split

type EcCoreGoal.rule += RBdHoareRnd of bdhoare_rnd_node

(* -------------------------------------------------------------------- *)
(* Raised when the event must be inferred from the postcondition, but the
   sampling assigns a tuple. *)
exception CannotInferEvent

(* Raised when the bounds [d2] / [d4] of form (5) depend on variables
   written by the statements preceding the sampling. *)
exception BoundWrittenByPrefix

(* -------------------------------------------------------------------- *)
(* The postcondition does not mention the sampled variables. *)
let bdhoare_rnd_post_indep env (bhs : bdHoareS) (lv : lvalue) =
  let fv = PV.fv env (bhs_po bhs).m (bhs_po bhs).inv in
  match lv with
  | LvVar (x,_) -> not (PV.mem_pv env x fv)
  | LvTuple pvs ->
    List.for_all (fun (x,_) -> not (PV.mem_pv env x fv)) pvs

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. Its side conditions (the
   last instruction is a sampling; an event can be inferred when needed) are
   part of it, so the checker re-validates them. *)
let bdhoare_rnd_subgoals
    (hyps : LDecl.hyps) (bhs : bdHoareS) (n : bdhoare_rnd_node) : form list
=
  let env = LDecl.toenv hyps in
  let (lv, distr), s =
    match s_last destr_rnd bhs.bhs_s with
    | Some x -> x
    | None -> failwith "bdhoare-rnd: the last instruction is not a sampling" in
  let m = fst bhs.bhs_m in
  let rb (f : ss_inv) = ss_inv_rebind f m in
  let ty_distr = proj_distr_ty env (e_ty distr) in
  let distr = EcFol.ss_inv_of_expr m distr in
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
  let is_post_indep = bdhoare_rnd_post_indep env bhs lv in
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
         | _ -> raise CannotInferEvent
  in
  let bound,pre_bound,binders =
    if is_bd_indep then
      bhs_bd bhs, {m;inv=f_true}, []
    else
      let bd_id = EcIdent.create "bd" in
      let bd = {m;inv=f_local bd_id treal} in
      bd, map_ss_inv2 f_eq (bhs_bd bhs) bd, [(bd_id,GTty treal)]
  in
  let nonneg_concl =
    f_forall_mems_ss_inv bhs.bhs_m
      (map_ss_inv2 f_real_le {m;inv=f_r0} (bhs_bd bhs)) in
  match n, bhs.bhs_cmp with
    | BRndInfer, FHle ->
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
        let post = POE.lift post in
        let concl = f_hoareS (snd bhs.bhs_m) pre s post in
        let concl = f_forall_simpl binders concl in
        [concl; nonneg_concl]
    | BRndInfer, _ ->
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
    | BRndEvent event, FHle ->
        let event = rb event in
        let bounded_distr = map_ss_inv2 f_real_le (map_ss_inv2 (f_mu env) distr event) bound in
        let pre = map_ss_inv2 f_and (bhs_pr bhs) pre_bound in
        let post = map_ss_inv2 f_anda bounded_distr (mk_event_cond event) in
        let post = POE.lift post in
        let concl = f_hoareS (snd bhs.bhs_m) pre s post in
        let concl = f_forall_simpl binders concl in
        [concl; nonneg_concl]
    | BRndEvent event, _ ->
        let event = rb event in
        let bounded_distr = map_ss_inv2 f_cmp (map_ss_inv2 (f_mu env) distr event) bound in
        let pre = map_ss_inv2 f_and (bhs_pr bhs) pre_bound in
        let post = map_ss_inv2 f_anda bounded_distr (mk_event_cond event) in
        let concl = f_bdHoareS (snd bhs.bhs_m) pre s post FHeq {m;inv=f_r1} in
        let concl = f_forall_simpl binders concl in
        [concl]
    | BRndSplit sp, _ ->
      let phi, d1, d2, d3, d4 =
        rb sp.brs_phi, rb sp.brs_d1, rb sp.brs_d2, rb sp.brs_d3, rb sp.brs_d4 in
      (* [d2] and [d4] are interpreted after [s] in [sgoal2] and [sgoal4],
         and in the initial memory in [bd_sgoal]: the two coincide only if
         [s] does not write them. *)
      List.iter (fun (d : ss_inv) ->
          if not (PV.indep env (s_write env s) (PV.fv env d.m d.inv)) then
            raise BoundWrittenByPrefix)
        [d2; d4];
      let event = match sp.brs_event with
        | None -> {m;inv=mk_event ~simpl:false ty_distr}
        | Some event -> rb event
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

(* -------------------------------------------------------------------- *)
(* Rule (TCB): instantiate the event and the bounds at the type of the
   sampled values, record them in the node, and build the subgoals through
   the shared core. *)
let t_bdhoare_rnd (r : bdhoare_rnd_rule) (tc : tcenv1) =
  let env = FApi.tc1_env tc in
  let bhs = tc1_as_bdhoareS tc in
  let (_, distr), _ = tc1_last_rnd tc bhs.bhs_s in
  let ty_distr = proj_distr_ty env (e_ty distr) in
  let n =
    match r.brr_info with
    | PNoRndParams ->
        BRndInfer
    | PSingleRndParam event ->
        BRndEvent (event ty_distr)
    | PMultRndParams ((phi, d1, d2, d3, d4), event) ->
        BRndSplit { brs_phi = phi; brs_d1 = d1; brs_d2 = d2;
                    brs_d3 = d3; brs_d4 = d4; brs_event = event ty_distr; }
    | PTwoRndParams _ ->
        tc_error !!tc "invalid arguments" in
  let sg =
    try  bdhoare_rnd_subgoals (FApi.tc1_hyps tc) bhs n
    with
    | CannotInferEvent ->
        tc_error !!tc "cannot infer a valid event, it must be provided"
    | BoundWrittenByPrefix ->
        tc_error !!tc
          "The bounds on the probability of the sampling (third and \
           fifth arguments) cannot depend on variables written by the \
           statements preceding the sampling" in
  FApi.xrule1 tc (RBdHoareRnd n) sg

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | RBdHoareRnd n ->
         Some (EcPlRecheck.checker_of "bdhoare-rnd" pf_as_bdhoareS
                 (fun hyps bhs -> bdhoare_rnd_subgoals hyps bhs n))
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node): the rule, then an attempt to close its
   non-negativity premise [forall &m, 0%r <= d], when it has one (the [<=]
   forms reducing the goal to a hoare judgement), with [t_trivial]. *)
let t_bdhoare_rnd_full (r : bdhoare_rnd_rule) (tc : tcenv1) =
  let gs = t_bdhoare_rnd r tc in
  let env = FApi.tc1_env tc in
  let bhs = tc1_as_bdhoareS tc in
  let (lv, _), _ = tc1_last_rnd tc bhs.bhs_s in
  let nonneg =
    bhs.bhs_cmp = FHle &&
      match r.brr_info with
      | PNoRndParams      -> not (bdhoare_rnd_post_indep env bhs lv)
      | PSingleRndParam _ -> true
      | _                 -> false in
  if nonneg then FApi.t_last (FApi.t_try t_trivial) gs else gs

(* -------------------------------------------------------------------- *)
(* Elaboration: the goal is known to be a [bdHoareS]. [rnd] takes no side
   and no position; the event ([ty -> bool]) and the bounds are typed in
   the goal's memory, the event once the type [ty] of the sampled values is
   known. *)
let process_bdhoare_rnd
    (side : oside) (pos : psemrndpos option) (info : rnd_tac_info_f) tc
=
  if EcUtils.is_some side || EcUtils.is_some pos then
    tc_error !!tc "invalid arguments";
  let info =
    match info with
    | PNoRndParams ->
        PNoRndParams

    | PSingleRndParam fp ->
        PSingleRndParam
          (fun t -> snd (TTC.tc1_process_Xhl_form tc (tfun t tbool) fp))

    | PMultRndParams ((phi, d1, d2, d3, d4), p) ->
        let p t = p |> EcUtils.omap (fun p -> snd (TTC.tc1_process_Xhl_form tc (tfun t tbool) p)) in
        let _, phi = TTC.tc1_process_Xhl_form tc tbool phi in
        let _, d1  = TTC.tc1_process_Xhl_form tc treal d1 in
        let _, d2  = TTC.tc1_process_Xhl_form tc treal d2 in
        let _, d3  = TTC.tc1_process_Xhl_form tc treal d3 in
        let _, d4  = TTC.tc1_process_Xhl_form tc treal d4 in
        PMultRndParams ((phi, d1, d2, d3, d4), p)

    | _ -> tc_error !!tc "invalid arguments"
  in
  t_bdhoare_rnd_full { brr_info = info } tc
