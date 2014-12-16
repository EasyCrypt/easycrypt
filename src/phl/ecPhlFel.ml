(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2014 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcPath
open EcTypes
open EcModules
open EcFol
open EcEnv
open EcPV

open EcCoreGoal

module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
let rec callable_oracles_f env modv os f =
  let f'   = NormMp.norm_xfun env f in
  let func = Fun.by_xpath f' env in

  match func.f_def with
  | FBalias _ ->
      assert false (* normal form *)

  | FBabs oi ->
      let called_fs =
        List.fold_left
          (fun s o ->
             if   PV.indep env modv (f_write env o)
             then s
             else EcPath.Sx.add o s)
          EcPath.Sx.empty oi.oi_calls
      in

      List.fold_left
        (callable_oracles_f env modv)
        os (EcPath.Sx.elements called_fs)

  | FBdef fdef ->
      let called_fs =
        List.fold_left
          (fun s o ->
            if   PV.indep env modv (f_write env o)
            then s
            else EcPath.Sx.add o s)
          EcPath.Sx.empty fdef.f_uses.us_calls in

      let f_written = f_write ~except:called_fs env f in

      if PV.indep env f_written modv then
        List.fold_left
          (callable_oracles_f env modv)
          os (EcPath.Sx.elements called_fs)
      else
        EcPath.Sx.add f os

and callable_oracles_s env modv os s =
  callable_oracles_is env modv os s.s_node

and callable_oracles_is env modv os is =
  List.fold_left (callable_oracles_i env modv) os is

and callable_oracles_sx env modv os ss =
  List.fold_left (callable_oracles_s env modv) os ss

and callable_oracles_i env modv os i =
  match i.i_node with
    | Scall  (_, f, _)   -> callable_oracles_f  env modv os f
    | Swhile (_, s)      -> callable_oracles_s  env modv os s
    | Sif    (_, s1, s2) -> callable_oracles_sx env modv os [s1; s2]

    | Sasgn _ | Srnd _ | Sassert _ -> os

    | Sabstract _ -> assert false (* FIXME *)

let callable_oracles_stmt env modv =
  callable_oracles_s env modv EcPath.Sx.empty

(* -------------------------------------------------------------------- *)
(* FIXME: do we have to subst more?                                     *)
let t_failure_event_r (at_pos, cntr, ash, q, f_event, pred_specs, inv) tc =
  let env, _, concl = FApi.tc1_eflat tc in

  let (pr, bd) =
    match concl.f_node with
    | Fapp ({ f_node =Fop (op, _) }, [pr; bd])
        when is_pr pr && EcPath.p_equal op EcCoreLib.CI_Real.p_real_le
      -> ((destr_pr pr), bd)

    | _ -> tc_error !!tc "a goal of the form Pr[ _ ] <= _ is required"
  in

  let m  = oget (Memory.byid pr.pr_mem env) in
  let f  = NormMp.norm_xfun env pr.pr_fun in
  let ev = pr.pr_event in

  let memenv, (_, fdef), _ =
    try  Fun.hoareS f env
    with _ -> tc_error !!tc "not applicable to abstract functions"
  in

  let s_hd, s_tl = s_split at_pos fdef.f_body in
  let fve        = PV.fv env mhr f_event in
  let fvc        = PV.fv env mhr cntr in
  let fv         = PV.union fve fvc in
  let os         = callable_oracles_stmt env fv (stmt s_tl) in

  (* check that bad event is only modified in oracles *)
  let written_except_os = s_write ~except:os env (stmt s_tl) in

  if not (PV.indep env written_except_os fv ) then
    tc_error_lazy !!tc (fun fmt ->
      Format.fprintf fmt
        "%s@. @[%a@] is not disjoint from @[%a@]@."
        "fail-event is modified outside oracles"
        (PV.pp env) written_except_os (PV.pp env) fv);

  (* subgoal on the bounds *)
  let bound_goal =
    let intval = f_int_intval (f_int 0) (f_int_sub q (f_int 1)) in
    let v = f_int_sum ash intval treal in
    f_real_le v bd
  in

  (* we must quantify over memories *)
  let mo = EcIdent.create "&m" in
  let post_goal =
    let subst = Fsubst.f_bind_mem Fsubst.f_subst_id mhr mo in
    let p = f_imp ev (f_and f_event (f_int_le cntr q)) in
    let p = Fsubst.f_subst subst p in
    f_forall_mems [mo, EcMemory.memtype m] p
  in

  (* not fail and cntr=0 holds at designated program point *)
  let init_goal =
    let p = f_and (f_not f_event) (f_eq cntr (f_int 0)) in
    let p = f_and_simpl p inv in
    f_hoareS memenv f_true (stmt s_hd) p
  in

  let oracle_goal o =
    let not_F_to_F_goal =
      let bound = f_app_simpl ash [cntr] treal in
      let pre = f_and (f_int_le (f_int 0) cntr) (f_not f_event) in
      let pre = f_and_simpl pre inv in
      let post = f_event in
      f_bdHoareF pre o post FHle bound
    in
    let old_cntr_id = EcIdent.create "c" in
    let old_b_id = EcIdent.create "b" in
    let old_cntr = f_local old_cntr_id tint in
    let old_b = f_local old_b_id tbool in
    let some_p =
      pred_specs
        |> List.findopt (fun (o', _) -> o = o')
        |> omap snd
        |> odfl f_true
    in
    let cntr_decr_goal =
      let pre  = f_and some_p (f_eq old_cntr cntr) in
      let pre = f_and_simpl pre inv in
      let post = f_and (f_int_lt old_cntr cntr) (f_int_le cntr q) in
      let post = f_and_simpl post inv in
        f_forall_simpl [old_cntr_id,GTty tint] (f_hoareF pre o post)
    in
    let cntr_stable_goal =
      let pre  = f_ands [f_not some_p;f_eq f_event old_b;f_eq cntr old_cntr] in
      let pre  = f_and_simpl pre inv in
      let post = f_ands [f_eq f_event old_b;f_eq cntr old_cntr] in
      let post = f_and_simpl post inv in
        f_forall_simpl
          [old_b_id,GTty tbool; old_cntr_id,GTty tint]
          (f_hoareF pre o post)
    in
    [not_F_to_F_goal;cntr_decr_goal;cntr_stable_goal]
  in

  let os_goals = List.concat (List.map oracle_goal (Sx.elements os)) in
  let concls   = bound_goal :: post_goal :: init_goal :: os_goals in
  let res = FApi.xmutate1 tc (`Fel (cntr, ash, q, f_event, pred_specs)) concls in
  res


(* -------------------------------------------------------------------- *)
let t_failure_event at_pos cntr ash q f_event pred_specs inv tc =
  let infos = (at_pos, cntr, ash, q, f_event, pred_specs, inv) in
  FApi.t_low1 "failure-event" t_failure_event_r infos tc

(* -------------------------------------------------------------------- *)
type pfel_t =
    pformula
  * pformula
  * pformula
  * pformula
  * (pgamepath * pformula) list
  * pformula option

let process_fel at_pos ((cntr, ash, q, f_event, pred_specs, o_inv) : pfel_t) tc =
  let env, hyps, concl = FApi.tc1_eflat tc in

  if EcEnv.Theory.by_path_opt EcCoreLib.CI_Sum.p_Sum env = None then 
    tacuerror "fel tactic cannot be used when theory Sum is not loaded";


  let f = match concl.f_node with
    | Fapp ({ f_node = Fop (op, _) }, [pr; _])
        when is_pr pr && EcPath.p_equal op EcCoreLib.CI_Real.p_real_le
      -> let { pr_fun = f } = destr_pr pr in f

    | _ -> tc_error !!tc "a goal of the form Pr[ _ ] <= _ is required"
  in
  let hyps    = fst (LDecl.hoareF f hyps) in
  let cntr    = TTC.pf_process_form !!tc hyps tint cntr in
  let ash     = TTC.pf_process_form !!tc hyps (tfun tint treal) ash in
  let q       = TTC.pf_process_form !!tc hyps tint q in
  let f_event = TTC.pf_process_form !!tc hyps tbool f_event in
  let inv     =
    o_inv
      |> omap (fun inv -> TTC.pf_process_form !!tc hyps tbool inv)
      |> odfl f_true
  in

  let process_pred (f,pre) =
    let env  = LDecl.toenv hyps in
    let f    = EcTyping.trans_gamepath env f in
    let penv = fst (LDecl.hoareF f hyps) in
      (f, TTC.pf_process_form !!tc penv tbool pre)
  in

  let pred_specs = List.map process_pred pred_specs in

  t_failure_event at_pos cntr ash q f_event pred_specs inv tc
