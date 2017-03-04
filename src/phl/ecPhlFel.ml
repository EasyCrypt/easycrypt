(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2017 - Inria
 *
 * Distributed under the terms of the CeCILL-C-V1 license
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
module IFEL : sig
  val loaded : env -> bool
  val felsum : form -> (form * form) -> form
end = struct
  open EcCoreLib

  let i_Fel  = "FelTactic"
  let p_Fel  = EcPath.pqname EcCoreLib.p_top i_Fel
  let p_List = [i_top; "List"]
  let p_BRA  = [i_top; "StdBigop"; "Bigreal"; "BRA"]

  let tlist =
    let tlist = EcPath.fromqsymbol (p_List, "list") in
    fun ty -> EcTypes.tconstr tlist [ty]

  let range =
    let rg = EcPath.fromqsymbol (p_List @ ["Range"], "range") in
    let rg = f_op rg [] (toarrow [tint; tint] (tlist tint)) in
    fun m n -> f_app rg [m; n] (tlist tint)

  let felsum =
    let bgty = [tpred tint; tfun tint treal; tlist tint] in
    let bg   = EcPath.fromqsymbol (p_BRA, "big") in
    let bg   = f_op bg [tint] (toarrow bgty treal) in
    let prT  = EcPath.fromqsymbol ([i_top; "Pred"], "predT") in
    let prT  = f_op prT [tint] (tpred tint) in
    fun f (m, n) -> f_app bg [prT; f; range m n] treal

  let loaded (env : env) =
    is_some (EcEnv.Theory.by_path_opt p_Fel env)
end

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

  let memenv, (fsig, fdef), _ =
    try  Fun.hoareS f env
    with _ -> tc_error !!tc "not applicable to abstract functions"
  in

  let s_hd, s_tl =
    let len = List.length fdef.f_body.s_node in
    if len < at_pos then
      tc_error !!tc
      "the size of the initialization code %i should be smaller than the size of the function body %i" at_pos len;
    s_split at_pos fdef.f_body in
  let fve        = PV.fv env mhr f_event in
  let fvc        = PV.fv env mhr cntr in
  let fvi        = PV.fv env mhr inv in
  let fv         = PV.union (PV.union fve fvc) fvi in
  let os         = callable_oracles_stmt env fv (stmt s_tl) in

  (* check that bad event, cntr and inv are only modified in oracles *)
  let written_except_os = s_write ~except:os env (stmt s_tl) in

  if not (PV.indep env written_except_os fv ) then
    tc_error_lazy !!tc (fun fmt ->
      Format.fprintf fmt
        "%s@. @[%a@] is not disjoint from @[%a@]@."
        "after initialization fail-event or invariant or counter is modified outside oracles"
        (PV.pp env) written_except_os (PV.pp env) fv);

  (* subgoal on the bounds *)
  let bound_goal =
    let v = IFEL.felsum ash (f_i0, q) in
    f_real_le v bd
  in

  (* we must quantify over memories *)
  let mo = EcIdent.create "&m" in
  let post_goal =
    let subst = Fsubst.f_bind_mem Fsubst.f_subst_id mhr mo in
    let p = f_imps [ev;inv] (f_and f_event (f_int_le cntr q)) in
    let p = Fsubst.f_subst subst p in
    f_forall_mems [mo, EcMemory.memtype m] p
  in

  (* not fail and cntr=0 and invariant holds at designated program point,
     under the pre that the initial parameter values correspond to arguments,
     and that the initial values of global read variables
     are equal to the initial memory *)

  let init_goal =
    let xs,gs = PV.ntr_elements (f_read env f) in
    let mh = fst memenv in
    let mi = pr.pr_mem in
    let f_xeq (x,ty) = f_eq (f_pvar x ty mh) (f_pvar x ty mi) in
    let eqxs = List.map f_xeq xs in
    let eqgs = List.map (fun m -> f_eqglob m mh m mi) gs in
    let eqparams =
      let vs = oget fsig.fs_anames in
      let f_x x = f_pvloc f x mh in
      f_eq (f_tuple (List.map f_x vs)) pr.pr_args in
    let pre = f_ands (eqparams :: (eqxs@eqgs)) in
    let p = f_and (f_not f_event) (f_eq cntr f_i0) in
    let p = f_and_simpl p inv in
    f_hoareS memenv pre (stmt s_hd) p
  in

  let oracle_goal o =
    let some_p =
      pred_specs
        |> List.ofind (fun (o', _) -> o = o')
        |> omap snd
        |> odfl f_true
    in

    let not_F_to_F_goal =
      let bound = f_app_simpl ash [cntr] treal in
      let pre = f_and (f_int_le f_i0 cntr) (f_int_lt cntr q) in
      let pre = f_and pre (f_not f_event) in
      let pre = f_and_simpl pre inv in
      let pre = f_and_simpl pre some_p in
      let post = f_event in
      f_bdHoareF pre o post FHle bound
    in
    let old_cntr_id = EcIdent.create "c" in
    let old_b_id = EcIdent.create "b" in
    let old_cntr = f_local old_cntr_id tint in
    let old_b = f_local old_b_id tbool in

    let cntr_decr_goal =
      let pre  = f_and some_p (f_eq old_cntr cntr) in
      let pre = f_and_simpl pre inv in
      let post = f_int_lt old_cntr cntr in
      let post = f_and_simpl post inv in
        f_forall_simpl [old_cntr_id,GTty tint] (f_hoareF pre o post)
    in
    let cntr_stable_goal =
      let pre  = f_ands [f_not some_p;f_eq f_event old_b;f_eq cntr old_cntr] in
      let pre  = f_and_simpl pre inv in
      let post = f_ands [f_eq f_event old_b;f_int_le old_cntr cntr] in
      let post = f_and_simpl post inv in
        f_forall_simpl
          [old_b_id,GTty tbool; old_cntr_id,GTty tint]
          (f_hoareF pre o post)
    in
    [not_F_to_F_goal;cntr_decr_goal;cntr_stable_goal]
  in

  let os_goals =
    List.concat (List.map oracle_goal (Sx.ntr_elements os)) in

  let concls = bound_goal :: post_goal :: init_goal :: os_goals in
  let res = FApi.xmutate1 tc (`Fel (cntr, ash, q, f_event, pred_specs)) concls in
  res


(* -------------------------------------------------------------------- *)
let t_failure_event at_pos cntr ash q f_event pred_specs inv tc =
  let infos = (at_pos, cntr, ash, q, f_event, pred_specs, inv) in
  FApi.t_low1 "failure-event" t_failure_event_r infos tc

(* -------------------------------------------------------------------- *)
let process_fel at_pos (infos : fel_info) tc =
  let env, hyps1, concl = FApi.tc1_eflat tc in

  if not (IFEL.loaded env) then
    tacuerror "fel: load the `FelTactic' theory first";

  let pr =
    match concl.f_node with
    | Fapp ({ f_node = Fop (op, _) }, [pr; _])
        when is_pr pr && EcPath.p_equal op EcCoreLib.CI_Real.p_real_le
      -> destr_pr pr
    | _ -> tc_error !!tc "a goal of the form Pr[ _ ] <= _ is required" in

  let hyps    = LDecl.inv_memenv1 hyps1 in
  let cntr    = TTC.pf_process_form !!tc hyps tint infos.pfel_cntr in
  let ash     = TTC.pf_process_form !!tc hyps (tfun tint treal) infos.pfel_asg in
  let hypsq   = LDecl.push_active (pr.pr_mem, None) hyps1 in
  let q       = TTC.pf_process_form !!tc hypsq tint infos.pfel_q in
  let f_event = TTC.pf_process_form !!tc hyps tbool infos.pfel_event in
  let inv     =
    infos.pfel_inv
      |> omap (fun inv -> TTC.pf_process_form !!tc hyps tbool inv)
      |> odfl f_true
  in

  let process_pred (f,pre) =
    let env  = LDecl.toenv hyps in
    let f    = EcTyping.trans_gamepath env f in
    let penv = fst (LDecl.hoareF f hyps) in
      (f, TTC.pf_process_form !!tc penv tbool pre)
  in

  let pred_specs = List.map process_pred infos.pfel_specs in

  t_failure_event at_pos cntr ash q f_event pred_specs inv tc
