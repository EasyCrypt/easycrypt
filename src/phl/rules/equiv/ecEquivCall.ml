(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcAst
open EcTypes
open EcModules
open EcFol
open EcEnv
open EcPV
open EcSubst

open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal

module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
(* Parameters of the two-sided equiv [call] rule: the specification of the
   called procedures. *)
type equiv_call = {
  ecall_pre  : ts_inv;   (* precondition P of the procedures *)
  ecall_post : ts_inv;   (* postcondition Q of the procedures *)
}

(* Parameters of the one-sided equiv [call] rule: the side of the call and
   the specification of the called procedure. *)
type equiv_call_onesided = {
  ecallos_side : side;     (* side of the call *)
  ecallos_pre  : ss_inv;   (* precondition P of the procedure *)
  ecallos_post : ss_inv;   (* postcondition Q of the procedure *)
}

type EcCoreGoal.rule +=
  | REquivCall         of equiv_call
  | REquivCallOneSided of equiv_call_onesided

(* -------------------------------------------------------------------- *)
(* Weakest precondition of [lvL <@ fL(aL) ~ lvR <@ fR(aR)] for the relation
   [post], given the specification [P ==> Q] of [fL ~ fR]:
     P[arg<1> := aL, arg<2> := aR] /\
       forall resultL resultR, forall (mod fL)<1> (mod fR)<2>,
         Q[res<1> := resultL, res<2> := resultR] =>
         post[lvL<1> := resultL, lvR<2> := resultR]
   [mods] are extra variables to generalize over, on each side. *)
let equiv_call_wp
   (hyps     : LDecl.hyps)
   ((ml, mr) : memory * memory)
   (contract : form * form)
  ?(mods     : EcPV.PV.t * EcPV.PV.t = (EcPV.PV.empty, EcPV.PV.empty))
   (call_l   : lvalue option * EcPath.xpath * expr list)
   (call_r   : lvalue option * EcPath.xpath * expr list)
   (post     : form)
=
  let env = LDecl.toenv hyps in

  let (fpre, fpost) = contract in
  let (lpl, fl, argsl) = call_l in
  let (lpr, fr, argsr) = call_r in

  let modil = EcPV.PV.union (fst mods) (f_write env fl) in
  let modir = EcPV.PV.union (snd mods) (f_write env fr) in

  let fsigl = (Fun.by_xpath fl env).f_sig in
  let fsigr = (Fun.by_xpath fr env).f_sig in

  let vresl = LDecl.fresh_id hyps "result_L" in
  let vresr = LDecl.fresh_id hyps "result_R" in
  let fresl = {ml; mr; inv = f_local vresl fsigl.fs_ret} in
  let fresr = {ml; mr; inv = f_local vresr fsigr.fs_ret} in

  let post =
       {ml; mr; inv = post}
    |> map_ts_inv_left2  (EcPlCall.wp_asgn_call ~mc:(ml, mr) env lpl) fresl
    |> map_ts_inv_right2 (EcPlCall.wp_asgn_call ~mc:(ml, mr) env lpr) fresr in

  let post = (ts_inv_rebind post ml mr).inv in

  let fpost =
    let s =
      PVM.of_list env
        [((pv_res, mr), fresr.inv); ((pv_res, ml), fresl.inv)] in
    PVM.subst env s fpost in

  let post =
       {ml; mr; inv = (f_imp_simpl fpost post)}
    |> generalize_mod_ts_inv env modil modir
  in

  let post = (ts_inv_rebind post ml mr).inv in

  let post =
    (f_forall_simpl
      [(vresl, GTty fsigl.fs_ret);
       (vresr, GTty fsigr.fs_ret)])
      post in

  let spre = EcPlCall.subst_args_call env ml (e_tuple argsl) PVM.empty in
  let spre = EcPlCall.subst_args_call env mr (e_tuple argsr) spre in

  f_anda_simpl (PVM.subst env spre fpre) post

(* -------------------------------------------------------------------- *)
(* Weakest precondition of [lv <@ f(a) ~ skip] (for [`Left]; symmetrically
   for [`Right]) for the relation [post], given the specification
   [P ==> Q] of [f] (one-sided, in the memory of [side]):
     P[arg<1> := a] /\
       forall result, forall (mod f)<1>,
         Q[res<1> := result] => post[lv<1> := result] *)
let equiv_call_onesided_wp
   (hyps     : LDecl.hyps)
   (side     : side)
   ((ml, mr) : memory * memory)
   (contract : form * form)
   (call     : lvalue option * EcPath.xpath * expr list)
   (post     : form)
=
  let env = LDecl.toenv hyps in

  let (fpre, fpost) = contract in
  let (lp, fname, args) = call in
  let me = sideif side ml mr in

  let wp_asgn_call_side env lv = sideif side
    (map_ts_inv_left2  (EcPlCall.wp_asgn_call ~mc:(ml,mr) env lv))
    (map_ts_inv_right2 (EcPlCall.wp_asgn_call ~mc:(ml,mr) env lv))
  in
  let generalize_mod_side = sideif side
    generalize_mod_left generalize_mod_right in

  let ss_inv_generalize_other_side inv = sideif side
    (ss_inv_generalize_right inv mr) (ss_inv_generalize_left inv ml) in

  let fsig  = (Fun.by_xpath fname env).f_sig in
  let vres  = LDecl.fresh_id hyps "result" in
  let fres  = { ml; mr; inv = f_local vres fsig.fs_ret; } in

  let post  = wp_asgn_call_side env lp fres { ml; mr; inv = post; } in
  let post  = (ts_inv_rebind post ml mr).inv in

  let subst = PVM.add env pv_res me fres.inv PVM.empty in

  let fpost = ss_inv_generalize_other_side { m = me; inv = fpost; } in
  let fpost = (ts_inv_rebind fpost ml mr).inv in
  let fpost = PVM.subst env subst fpost in

  let fpre  = ss_inv_generalize_other_side { m = me; inv = fpre ; } in
  let fpre  = (ts_inv_rebind fpre ml mr).inv in

  let modi  = f_write env fname in
  let post  = f_imp_simpl fpost post in
  let post  = generalize_mod_side env modi { ml; mr; inv = post } in
  let post  = (ts_inv_rebind post ml mr).inv in
  let post  = f_forall_simpl [(vres, GTty fsig.fs_ret)] post in
  let spre  = EcPlCall.subst_args_call env me (e_tuple args) PVM.empty in

  f_anda_simpl (PVM.subst env spre fpre) post

(* -------------------------------------------------------------------- *)
(* Pure cores shared by the rules and their checkers. Their side
   conditions (the statements are single calls — resp. a single call and
   the empty statement —, and the precondition is the weakest
   precondition) are part of them, so the checkers re-validate them. *)
let equiv_call_subgoals (hyps : LDecl.hyps) (es : equivS) (n : equiv_call) =
  let ml, mr = fst es.es_ml, fst es.es_mr in
  let fpre  = ts_inv_rebind n.ecall_pre  ml mr in
  let fpost = ts_inv_rebind n.ecall_post ml mr in
  let (_, fl, _) as call_l = EcPlCall.single_call "equiv-call" es.es_sl in
  let (_, fr, _) as call_r = EcPlCall.single_call "equiv-call" es.es_sr in
  let wp =
    equiv_call_wp hyps (ml, mr) (fpre.inv, fpost.inv) call_l call_r
      (es_po es).inv in
  if not (EcReduction.is_conv hyps (es_pr es).inv wp) then
    failwith "equiv-call: the precondition is not the expected one";
  [f_equivF fpre fl fr fpost]

let equiv_call_onesided_subgoals
    (hyps : LDecl.hyps) (es : equivS) (n : equiv_call_onesided)
=
  let side = n.ecallos_side in
  let ml, mr = fst es.es_ml, fst es.es_mr in
  let me = sideif side ml mr in
  let fpre  = ss_inv_rebind n.ecallos_pre  me in
  let fpost = ss_inv_rebind n.ecallos_post me in
  let s, so = sideif side (es.es_sl, es.es_sr) (es.es_sr, es.es_sl) in
  let (_, f, _) as call = EcPlCall.single_call "equiv-call-onesided" s in
  if not (List.is_empty so.s_node) then
    failwith "equiv-call-onesided: the other statement is not empty";
  let wp =
    equiv_call_onesided_wp hyps side (ml, mr) (fpre.inv, fpost.inv) call
      (es_po es).inv in
  if not (EcReduction.is_conv hyps (es_pr es).inv wp) then
    failwith "equiv-call-onesided: the precondition is not the expected one";
  [f_bdHoareF fpre f fpost FHeq { m = fpost.m; inv = f_r1; }]

(* -------------------------------------------------------------------- *)
(* Rules (TCB). *)
let t_equiv_call (n : equiv_call) (tc : tcenv1) =
  let es = tc1_as_equivS tc in
  let sg =
    try  equiv_call_subgoals (FApi.tc1_hyps tc) es n
    with Failure msg -> tc_error !!tc "%s" msg in
  FApi.xrule1 tc (REquivCall n) sg

let t_equiv_call_onesided (n : equiv_call_onesided) (tc : tcenv1) =
  let es = tc1_as_equivS tc in
  let sg =
    try  equiv_call_onesided_subgoals (FApi.tc1_hyps tc) es n
    with Failure msg -> tc_error !!tc "%s" msg in
  FApi.xrule1 tc (REquivCallOneSided n) sg

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | REquivCall n ->
         Some (EcPlRecheck.checker_of "equiv-call" pf_as_equivS
                 (fun hyps es -> equiv_call_subgoals hyps es n))
     | REquivCallOneSided n ->
         Some (EcPlRecheck.checker_of "equiv-call-onesided" pf_as_equivS
                 (fun hyps es -> equiv_call_onesided_subgoals hyps es n))
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node): [seq] before the final calls (resp. before the
   final call on one side, at the end of the other one), with their
   weakest precondition as intermediate relation, then close the calls
   with the rules. The specification premise comes first. *)
let t_equiv_call_last (n : equiv_call) (tc : tcenv1) =
  let hyps = FApi.tc1_hyps tc in
  let es   = tc1_as_equivS tc in
  let ml, mr = fst es.es_ml, fst es.es_mr in
  let fpre  = ts_inv_rebind n.ecall_pre  ml mr in
  let fpost = ts_inv_rebind n.ecall_post ml mr in
  let call_l, _ = tc1_last_call tc es.es_sl in
  let call_r, _ = tc1_last_call tc es.es_sr in
  let mid =
    equiv_call_wp hyps (ml, mr) (fpre.inv, fpost.inv) call_l call_r
      (es_po es).inv in
  let at = EcMatching.Position.gap_before_last_n 1 in
  FApi.t_swap_goals 0 1
    (FApi.t_seqsub
       (EcEquivSeq.t_equiv_seq
          { esr_at = (at, at); esr_mid = { ml; mr; inv = mid; } })
       [t_id; t_equiv_call n]
       tc)

let t_equiv_call_onesided_last (n : equiv_call_onesided) (tc : tcenv1) =
  let hyps = FApi.tc1_hyps tc in
  let es   = tc1_as_equivS tc in
  let side = n.ecallos_side in
  let ml, mr = fst es.es_ml, fst es.es_mr in
  let me = sideif side ml mr in
  let fpre  = ss_inv_rebind n.ecallos_pre  me in
  let fpost = ss_inv_rebind n.ecallos_post me in
  let call, _ = tc1_last_call tc (sideif side es.es_sl es.es_sr) in
  let mid =
    equiv_call_onesided_wp hyps side (ml, mr) (fpre.inv, fpost.inv) call
      (es_po es).inv in
  let at = EcMatching.Position.(sideif side
    (gap_before_last_n 1, codegap1_end)
    (codegap1_end, gap_before_last_n 1)) in
  FApi.t_swap_goals 0 1
    (FApi.t_seqsub
       (EcEquivSeq.t_equiv_seq { esr_at = at; esr_mid = { ml; mr; inv = mid; } })
       [t_id; t_equiv_call_onesided n]
       tc)

(* -------------------------------------------------------------------- *)
(* The specification [equiv [fl ~ fr : ={arg} /\ I ==> ={res} /\ I]] of
   [call (: I)] (with [={glob A}] for abstract procedures of [A]). *)
let equiv_call_inv_spec (pf : proofenv) env (inv : ts_inv) fl fr =
  let ml, mr = inv.ml, inv.mr in
  match NormMp.is_abstract_fun fl env with
  | true ->
    let (topl, _, _, sigl),
      (topr, _, _  , sigr) = EcLowPhlGoal.abstract_info2 env fl fr in
    let eqglob = ts_inv_eqglob topl ml topr mr in
    let lpre = [eqglob;inv] in
    let eq_params =
      ts_inv_eqparams
        sigl.fs_arg sigl.fs_anames ml
        sigr.fs_arg sigr.fs_anames mr in
    let eq_res = ts_inv_eqres sigl.fs_ret ml sigr.fs_ret mr in
    let pre    = map_ts_inv f_ands (eq_params::lpre) in
    let post   = map_ts_inv f_ands [eq_res; eqglob; inv] in
      f_equivF pre fl fr post

  | false ->
      let defl = EcEnv.Fun.by_xpath fl env in
      let defr = EcEnv.Fun.by_xpath fr env in
      let sigl, sigr = defl.f_sig, defr.f_sig in

      let error s tl tr =
        let ppe = EcPrinting.PPEnv.ofenv env in
        tc_error pf "@[The procedures do not have the same %s types:@]@;<2 2>\
          @[<v>Left side:  @[<h>%a@]@,\
            Right side: @[<h>%a@]@]@;<2 0>\
          A full contract cannot be inferred; consider providing a full contract using@;<2 2>\
            call (: ...==> ...)@,"
        s
        (EcPrinting.pp_type ppe) tl
        (EcPrinting.pp_type ppe) tr
      in

      if not (EcReduction.EqTest.for_type env sigl.fs_arg sigr.fs_arg)
      then error "argument" sigl.fs_arg sigr.fs_arg;

      if not (EcReduction.EqTest.for_type env sigl.fs_ret sigr.fs_ret)
      then error "return" sigl.fs_ret sigr.fs_ret;

      let eq_params =
        ts_inv_eqparams
          sigl.fs_arg sigl.fs_anames ml
          sigr.fs_arg sigr.fs_anames mr in
      let eq_res = ts_inv_eqres sigl.fs_ret ml sigr.fs_ret mr in
      let pre = map_ts_inv2 f_and eq_params inv in
      let post = map_ts_inv2 f_and eq_res inv in
        f_equivF pre fl fr post

(* -------------------------------------------------------------------- *)
(* Elaboration: the goal is known to be an [equivS]. Types the cut of
   [call]: the specification of the last call(s). *)
let process_equiv_call_cut (side : oside) (info : call_info) (tc : tcenv1) =
  let hyps, concl = FApi.tc1_flat tc in
  let es = destr_equivS concl in
  let last_fs () =
    let (_,fl,_) = fst (tc1_last_call tc es.es_sl) in
    let (_,fr,_) = fst (tc1_last_call tc es.es_sr) in
    (fl, fr) in

  match info, side with
  | CI_spec (pre, epost), None ->
    let fl, fr = last_fs () in
    let (ml, mr) = (EcIdent.create "&1", EcIdent.create "&2") in
    let penv, qenv = LDecl.equivF ml mr fl fr hyps in
    let pre  = TTC.pf_process_form !!tc penv tbool pre  in
    let post = TTC.pf_process_form !!tc qenv tbool epost.pnormal in
    (f_equivF {ml;mr;inv=pre} fl fr {ml;mr;inv=post}, t_id)

  | CI_spec (pre, epost), Some side ->
    let fstmt = sideif side es.es_sl es.es_sr in
    let m = sideif side (EcIdent.create "&1") (EcIdent.create "&2") in
    let (_,f,_) = fst (tc1_last_call tc fstmt) in
    let penv, qenv = LDecl.hoareF m f hyps in
    let pre  = TTC.pf_process_form !!tc penv tbool pre  in
    let post = TTC.pf_process_form !!tc qenv tbool epost.pnormal in
    (f_bdHoareF {m;inv=pre} f {m;inv=post} FHeq {m;inv=f_r1}, t_id)

  | (CI_inv _ | CI_upto _), Some _ ->
    tc_error !!tc "cannot specify side for call with invariants"

  | CI_inv inv, None ->
    let ml, mr = fst es.es_ml, fst es.es_mr in
    let fl, fr = last_fs () in
    let mel, mer = EcMemory.abstract ml, EcMemory.abstract mr in
    let hyps = LDecl.push_active_ts mel mer hyps in
    let env  = LDecl.toenv hyps in
    let inv = TTC.pf_process_form !!tc hyps tbool inv in
    let inv = {ml;mr; inv} in
    let t_spec tc =
      FApi.t_firsts t_trivial 2 (EcPhlFun.t_fun (Inv_ts inv) tc) in
    (equiv_call_inv_spec !!tc env inv fl fr, t_spec)

  | CI_upto info, None ->
    let env = FApi.tc1_env tc in
    let ml, mr = fst es.es_ml, fst es.es_mr in
    let fl, fr = last_fs () in
    let weakened_pre,bad,invP,invQ = EcPhlFun.process_fun_upto_info info tc in
    let bad2 = ss_inv_generalize_as_right bad ml mr in
    let invP = ts_inv_rebind invP ml mr in
    let invQ = ts_inv_rebind invQ ml mr in
    let (topl,fl,_,sigl),
        (topr,fr,_  ,sigr) = EcLowPhlGoal.abstract_info2 env fl fr in
    let eqglob = ts_inv_eqglob topl ml topr mr in
    let lpre = [eqglob;invP] in
    let eq_params =
      ts_inv_eqparams
        sigl.fs_arg sigl.fs_anames ml
        sigr.fs_arg sigr.fs_anames mr in
    let eq_res = ts_inv_eqres sigl.fs_ret ml sigr.fs_ret mr in
    let pre    = map_ts_inv3 f_if_simpl bad2 invQ (map_ts_inv f_ands (eq_params::lpre)) in
    let post   = map_ts_inv3 f_if_simpl bad2 invQ (map_ts_inv f_ands [eq_res;eqglob;invP]) in
    let t_tr = FApi.t_or (t_assumption `Conv) t_trivial in
    let t_spec tc =
      FApi.t_firsts t_tr 3
        (EcPhlFun.t_equivF_abs_upto weakened_pre bad invP invQ tc) in
    (f_equivF pre fl fr post, t_spec)
