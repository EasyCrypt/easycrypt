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
open EcPath
open EcTypes
open EcFol
open EcMemory
open EcModules
open EcEnv
open EcPV

open EcCoreGoal
open EcLowPhlGoal

module TTC = EcProofTyping

(* FIXME: oracles should ensure they preserve the state of the adversaries
 *
 * Two solutions:
 *   - add the equalities in the pre and post.
 *   - ensure that oracle doesn't write the adversaries states
 *
 * See [ospec] in [equivF_abs_spec / equivF_abs_upto] *)

(* -------------------------------------------------------------------- *)
let check_oracle_use (_pf : proofenv) env adv o =
  let restr = { mr_empty with
                mr_mpaths = { mr_empty.mr_mpaths with
                              ur_neg = Sm.singleton adv; }} in

  (* This only checks the memory restrictions. *)
  EcTyping.check_mem_restr_fun env o restr

let check_concrete pf env f =
  if NormMp.is_abstract_fun f env then
    tc_error_lazy pf (fun fmt ->
      let ppe = EcPrinting.PPEnv.ofenv env in
      Format.fprintf fmt
        "The function %a is abstract, it should be concrete"
        (EcPrinting.pp_funname ppe) f)

(* -------------------------------------------------------------------- *)
let lossless_hyps env top sub =
  let clear_to_top restr =
    let mr_mpaths = { (ur_empty Sm.empty) with ur_neg = Sm.singleton top } in
    { restr with mr_xpaths = ur_empty Sx.empty;
                 mr_mpaths = mr_mpaths } in

  let sig_ = EcEnv.NormMp.sig_of_mp env top in
  let bd =
    List.map
      (fun (id, mt) ->
         (id, GTmodty { mt with mt_restr = clear_to_top mt.mt_restr } )
      ) sig_.mis_params
  in
  (* WARN: this implies that the oracle do not have access to top *)
  let args  = List.map (fun (id,_) -> EcPath.mident id) sig_.mis_params in
  let concl = f_losslessF (EcPath.xpath (EcPath.m_apply top args) sub) in
  let calls =
    let name = sub in
    (EcSymbols.Msym.find name sig_.mis_restr.mr_oinfos) |> OI.allowed
  in
  let hyps = List.map f_losslessF calls in
    f_forall bd (f_imps hyps concl)

(* -------------------------------------------------------------------- *)
let subst_pre env fs (m : memory) s =
  match fs.fs_anames with
  | Some lv ->
      let v = List.map (fun v -> f_pvloc v m) lv in
        PVM.add env pv_arg m (f_tuple v) s
  | None -> s

(* ------------------------------------------------------------------ *)
let t_hoareF_fun_def_r tc =
  let env = FApi.tc1_env tc in
  let hf = tc1_as_hoareF tc in
  let f = NormMp.norm_xfun env hf.hf_f in
  check_concrete !!tc env f;
  let (memenv, (fsig, fdef), env) = Fun.hoareS f env in
  let m = EcMemory.memory memenv in
  let fres = odfl f_tt (omap (form_of_expr m) fdef.f_ret) in
  let post = PVM.subst1 env pv_res m fres hf.hf_po in
  let pre  = PVM.subst env (subst_pre env fsig m PVM.empty) hf.hf_pr in
  let concl' = f_hoareS memenv pre fdef.f_body post in
  FApi.xmutate1 tc `FunDef [concl']

(* ------------------------------------------------------------------ *)
let t_choareF_fun_def_r tc =
  let env = FApi.tc1_env tc in
  let chf = tc1_as_choareF tc in
  let f = NormMp.norm_xfun env chf.chf_f in
  check_concrete !!tc env f;
  let (memenv, (fsig, fdef), env) = Fun.hoareS f env in
  let m = EcMemory.memory memenv in
  let fres = odfl f_tt (omap (form_of_expr m) fdef.f_ret) in
  let post = PVM.subst1 env pv_res m fres chf.chf_po in
  let spre = subst_pre env fsig m PVM.empty in
  let pre = PVM.subst env spre chf.chf_pr in
  let c   = PVM.subst_cost env spre chf.chf_co in
  let c = match fdef.f_ret with
    | None -> c
    | Some ret ->
      EcFol.cost_sub_self
        c (EcFol.cost_of_expr_any memenv ret) in
  let concl' = f_cHoareS memenv pre fdef.f_body post c in
  FApi.xmutate1 tc `FunDef [concl']

(* ------------------------------------------------------------------ *)
let t_bdhoareF_fun_def_r tc =
  let env = FApi.tc1_env tc in
  let bhf = tc1_as_bdhoareF tc in
  let f = NormMp.norm_xfun env bhf.bhf_f in
  check_concrete !!tc env f;
  let (memenv, (fsig, fdef), env) = Fun.hoareS f env in
  let m = EcMemory.memory memenv in
  let fres = odfl f_tt (omap (form_of_expr m) fdef.f_ret) in
  let post = PVM.subst1 env pv_res m fres bhf.bhf_po in
  let spre = subst_pre env fsig m PVM.empty in
  let pre = PVM.subst env spre bhf.bhf_pr in
  let bd  = PVM.subst env spre bhf.bhf_bd in
  let concl' = f_bdHoareS memenv pre fdef.f_body post bhf.bhf_cmp bd in
  FApi.xmutate1 tc `FunDef [concl']

(* ------------------------------------------------------------------ *)
let t_equivF_fun_def_r tc =
  let env = FApi.tc1_env tc in
  let ef = tc1_as_equivF tc in
  let fl = NormMp.norm_xfun env ef.ef_fl in
  let fr = NormMp.norm_xfun env ef.ef_fr in
  check_concrete !!tc env fl; check_concrete !!tc env fr;
  let (menvl, eqsl, menvr, eqsr, env) = Fun.equivS fl fr env in
  let (fsigl, fdefl) = eqsl in
  let (fsigr, fdefr) = eqsr in
  let ml = EcMemory.memory menvl in
  let mr = EcMemory.memory menvr in
  let fresl = odfl f_tt (omap (form_of_expr ml) fdefl.f_ret) in
  let fresr = odfl f_tt (omap (form_of_expr mr) fdefr.f_ret) in
  let s = PVM.add env pv_res ml fresl PVM.empty in
  let s = PVM.add env pv_res mr fresr s in
  let post = PVM.subst env s ef.ef_po in
  let s = subst_pre env fsigl ml PVM.empty in
  let s = subst_pre env fsigr mr s in
  let pre = PVM.subst env s ef.ef_pr in
  let concl' = f_equivS menvl menvr pre fdefl.f_body fdefr.f_body post in
  FApi.xmutate1 tc `FunDef [concl']

(* -------------------------------------------------------------------- *)
let t_hoareF_fun_def   = FApi.t_low0 "hoare-fun-def"   t_hoareF_fun_def_r
let t_choareF_fun_def  = FApi.t_low0 "choare-fun-def"  t_choareF_fun_def_r
let t_bdhoareF_fun_def = FApi.t_low0 "bdhoare-fun-def" t_bdhoareF_fun_def_r
let t_equivF_fun_def   = FApi.t_low0 "equiv-fun-def"   t_equivF_fun_def_r

(* -------------------------------------------------------------------- *)
let t_fun_def_r tc =
  let th  = t_hoareF_fun_def
  and tch = t_choareF_fun_def
  and tbh = t_bdhoareF_fun_def
  and te  = t_equivF_fun_def in

  t_hF_or_chF_or_bhF_or_eF ~th ~tch ~tbh ~te tc

let t_fun_def = FApi.t_low0 "fun-def" t_fun_def_r

(* -------------------------------------------------------------------- *)
type abs_inv_inf = (xpath * form) list * (xpath * cost) list

let process_p_abs_inv_inf tc hyps p_abs_inv_inf =
  let env = LDecl.toenv hyps in
  let xv = List.map (fun (f,v) ->
      EcTyping.trans_gamepath env f,
      TTC.pf_process_form !!tc hyps tint v
    ) p_abs_inv_inf.ci_vrnts

  and xc = List.map (fun (f,c) ->
      EcTyping.trans_gamepath env f,
      TTC.pf_process_cost !!tc hyps (tfun tint tint) c
    ) p_abs_inv_inf.ci_oracles in

  (xv, xc)


type inv_inf =  [
  | `Std     of cost
  | `CostAbs of (xpath * form) list * (xpath * cost) list
]

(* -------------------------------------------------------------------- *)
module FunAbsLow = struct
  (* ------------------------------------------------------------------ *)
  let hoareF_abs_spec _pf env f inv =
    let (top, _, oi, _) = EcLowPhlGoal.abstract_info env f in
    let fv = PV.fv env mhr inv in
    PV.check_depend env fv top;
    let ospec o = f_hoareF inv o inv in
    let sg = List.map ospec (OI.allowed oi) in
    (inv, inv, sg)

  (* ------------------------------------------------------------------ *)
  let choareF_abs_spec pf_ env f inv (xv, xc : abs_inv_inf) =
    let (top, _, oi, _) = EcLowPhlGoal.abstract_info env f in
    let ppe = EcPrinting.PPEnv.ofenv env in

    (* We check that the invariant and variants variables cannot be modified
       by the adversary. *)
    let fv_inv   = PV.fv env mhr inv in
    let fv_vrnts = List.map (fun (_,v) -> PV.fv      env mhr v) xv in
    PV.check_depend env fv_inv top;
    List.iter (fun fv -> PV.check_depend env fv top) fv_vrnts;

    (* TODO: (Adrien) why are we checking this for bdhoareF_abs_spec, and is
       it needed here?*)
    (* check_oracle_use pf env top o; *)

    let cost_orcl oi o = match OI.cost oi o with
      | `Bounded cbd -> cbd
      | `Zero -> f_i0
      | `Unbounded ->
        tc_error pf_ "the number of calls to %a is unbounded"
          (EcPrinting.pp_funname ppe) o in

    (* We create the oracles invariants *)
    let oi_self, oi_costs = match OI.costs oi with
      | `Unbounded ->
        tc_error pf_ "%a is unbounded" (EcPrinting.pp_funname ppe) f
      | `Bounded (self,costs) -> self, costs in

    (* If [f] can call [o] at most zero times, we remove it. *)
    let ois = OI.allowed oi
              |> List.filter (fun o ->
                  not @@ opt_equal f_equal
                    (Mx.find_opt o oi_costs)
                    (Some f_i0)) in

    let ospec o_called =
      let k_called = ref None in
      (* forall ks. call_bounds =>
         hoare [{ inv /\ pre_eqs } o_called {inv /\ post_eqs }] *)
      let ks, call_bounds, pre_eqs, post_eqs =
        List.fold_left (fun (ks, call_bounds, pre_eqs, post_eqs) o ->
            let k_id = EcIdent.create ("z" ^ EcPath.xbasename o) in
            let k = f_local k_id tint in

            if x_equal o o_called then k_called := Some k;

            let cbd = cost_orcl oi o in
            let call_bound =
              if x_equal o o_called
              then f_and (f_int_le f_i0 k) (f_int_lt k cbd)
              else f_and (f_int_le f_i0 k) (f_int_le k cbd) in

            match List.find_opt (fun (x,_) -> x_equal x o) xv with
            | None ->
              if x_equal o o_called
              then k_id :: ks, call_bound :: call_bounds, pre_eqs, post_eqs
              else         ks,               call_bounds, pre_eqs, post_eqs
            | Some (_,vrnt) ->
              let pre_eq  =
                f_int_le vrnt k
              and post_eq =
                if x_equal o o_called
                then f_int_le vrnt (f_int_add k f_i1)
                else f_int_le vrnt k in

              k_id :: ks,
              call_bound :: call_bounds,
              pre_eq :: pre_eqs,
              post_eq :: post_eqs
          ) ([],[],[],[]) ois in

      let ks = List.map (fun k_id -> (k_id,GTty tint)) ks in
      let call_bounds, pre_eqs, post_eqs = f_ands0_simpl call_bounds,
                                           f_ands0_simpl pre_eqs,
                                           f_ands0_simpl post_eqs in

      let pre_inv  = f_and_simpl pre_eqs inv
      and post_inv = f_and_simpl post_eqs inv in

      (* We now compute the cost of the call to [o_called]. *)
      let cost = List.find_opt (fun (x,_) -> x_equal x o_called) xc in
      let cost = match cost with
        | None ->
          tc_error pf_ "no cost has been supplied for %a"
            (EcPrinting.pp_funname ppe) o_called
        | Some (_,cost) -> cost in
      let k_cost = cost_app cost [oget !k_called] in

      let form = f_cHoareF pre_inv o_called post_inv k_cost in
      f_forall_simpl ks (f_imp_simpl call_bounds form) in

    (* We have the conditions for the oracles. *)
    let sg = List.map ospec ois in

    (* Finally, we compute the conclusion. *)
    let eqs =
      List.map (fun o ->
          let o_vrnt = List.find_opt (fun (x,_) -> x_equal x o) xv in
          let pre_eq = match o_vrnt with
            | None          -> f_true
            | Some (_,vrnt) -> f_int_le vrnt f_i0 in


          let cbd = cost_orcl oi o in
          let post_eq = match o_vrnt with
            | None          ->
              f_true
            | Some (_,vrnt) -> f_int_le vrnt cbd  in

          pre_eq, post_eq) ois in

    (* hoare [{ inv /\ pre_eqs } f {inv /\ post_eqs }] *)
    let pre_eqs, post_eqs = List.split eqs in
    let pre_eqs, post_eqs = f_ands0_simpl pre_eqs,
                            f_ands0_simpl post_eqs in

    let pre_inv  = f_and_simpl pre_eqs inv
    and post_inv = f_and_simpl post_eqs inv in

    let fn_orcl = EcPath.xpath top f.x_sub in
    let f_cb = { cb_cost   = oi_self;
                 cb_called = f_i1; } in
    let f_cost = cost_r f_i0 (Mx.singleton fn_orcl f_cb)  in

    let orcls_cost = List.map (fun o ->
        let cbd = cost_orcl oi o in
        (* Cost of a call to [o]. *)
        let o_cost = snd @@ List.find (fun (x,_) -> x_equal x o) xc in

        (* Upper-bound on the costs of [o]'s calls. *)
        EcPhlWhile.ICHOARE.choare_sum o_cost (f_i0, cbd)
      ) ois in
    let total_cost =
      List.fold_left (cost_op env f_int_add_simpl) f_cost orcls_cost in

    (pre_inv, post_inv, total_cost, sg)


  (* ------------------------------------------------------------------ *)
  let bdhoareF_abs_spec pf env f inv =
    let (top, _, oi, _) = EcLowPhlGoal.abstract_info env f in
    let fv = PV.fv env mhr inv in

    PV.check_depend env fv top;
    let ospec o =
      check_oracle_use pf env top o;
      f_bdHoareF inv o inv FHeq f_r1 in

    let sg = List.map ospec (OI.allowed oi) in
    (inv, inv, lossless_hyps env top f.x_sub :: sg)

  (* ------------------------------------------------------------------ *)
  let equivF_abs_spec pf env fl fr inv =
    let (topl, _fl, oil, sigl), (topr, _fr, oir, sigr) =
      EcLowPhlGoal.abstract_info2 env fl fr
    in

    let ml, mr = mleft, mright in
    let fvl = PV.fv env ml inv in
    let fvr = PV.fv env mr inv in
    PV.check_depend env fvl topl;
    PV.check_depend env fvr topr;
    let eqglob = f_eqglob topl ml topr mr in

    let ospec o_l o_r =
      let use =
        try
          check_oracle_use pf env topl o_l;
          if   EcPath.x_equal o_l o_r
          then check_oracle_use pf env topl o_r;
          false
        with _ when OI.is_in oil -> true
      in

      let fo_l = EcEnv.Fun.by_xpath o_l env in
      let fo_r = EcEnv.Fun.by_xpath o_r env in

      let eq_params =
        f_eqparams
          fo_l.f_sig.fs_arg fo_l.f_sig.fs_anames ml
          fo_r.f_sig.fs_arg fo_r.f_sig.fs_anames mr in

      let eq_res =
        f_eqres fo_l.f_sig.fs_ret ml fo_r.f_sig.fs_ret mr in

      let invs = if use then [eqglob; inv] else [inv] in
      let pre  = EcFol.f_ands (eq_params :: invs) in
      let post = EcFol.f_ands (eq_res :: invs) in
      f_equivF pre o_l o_r post
    in

    let sg = List.map2 ospec (OI.allowed oil) (OI.allowed oir) in

    let eq_params =
      f_eqparams
        sigl.fs_arg sigl.fs_anames ml
        sigr.fs_arg sigr.fs_anames mr in

    let eq_res = f_eqres sigl.fs_ret ml sigr.fs_ret mr in
    let lpre   = if OI.is_in oil then [eqglob;inv] else [inv] in
    let pre    = f_ands (eq_params::lpre) in
    let post   = f_ands [eq_res; eqglob; inv] in

    (pre, post, sg)
end

(* ------------------------------------------------------------------ *)
let t_hoareF_abs_r inv tc =
  let env = FApi.tc1_env tc in
  let hf = tc1_as_hoareF tc in
  let pre, post, sg = FunAbsLow.hoareF_abs_spec !!tc env hf.hf_f inv in

  let tactic tc = FApi.xmutate1 tc `FunAbs sg in
  FApi.t_last tactic (EcPhlConseq.t_hoareF_conseq pre post tc)

(* ------------------------------------------------------------------ *)
let t_choareF_abs_r inv inv_inf tc =
  let env = FApi.tc1_env tc in
  let hf = tc1_as_choareF tc in
  let pre, post, cost, sg =
    FunAbsLow.choareF_abs_spec !!tc env hf.chf_f inv inv_inf in

  let tactic tc = FApi.xmutate1 tc `FunAbs sg in
  FApi.t_last tactic (EcPhlConseq.t_cHoareF_conseq_full pre post cost tc)


(* ------------------------------------------------------------------ *)
let t_bdhoareF_abs_r inv tc =
  let env = FApi.tc1_env tc in
  let bhf = tc1_as_bdhoareF tc in

  match bhf.bhf_cmp with
  | FHeq when f_equal bhf.bhf_bd f_r1 ->
      let pre, post, sg =
        FunAbsLow.bdhoareF_abs_spec !!tc env bhf.bhf_f inv
      in
      let tactic tc = FApi.xmutate1 tc `FunAbs sg in
      FApi.t_last tactic (EcPhlConseq.t_bdHoareF_conseq pre post tc)

  | _ -> tc_error !!tc "bound must of \"= 1\""

(* ------------------------------------------------------------------ *)
let t_equivF_abs_r inv tc =
  let env = FApi.tc1_env tc in
  let ef = tc1_as_equivF tc in
  let pre, post, sg =
    FunAbsLow.equivF_abs_spec !!tc env ef.ef_fl ef.ef_fr inv
  in

  let tactic tc = FApi.xmutate1 tc `FunAbs sg in
  FApi.t_last tactic (EcPhlConseq.t_equivF_conseq pre post tc)

(* -------------------------------------------------------------------- *)
let t_hoareF_abs   = FApi.t_low1 "hoare-fun-abs"   t_hoareF_abs_r
let t_choareF_abs  = FApi.t_low2 "choare-fun-abs"  t_choareF_abs_r
let t_bdhoareF_abs = FApi.t_low1 "bdhoare-fun-abs" t_bdhoareF_abs_r
let t_equivF_abs   = FApi.t_low1 "equiv-fun-abs"   t_equivF_abs_r

(* -------------------------------------------------------------------- *)
module UpToLow = struct
  (* ------------------------------------------------------------------ *)
  let equivF_abs_upto pf env fl fr bad invP invQ =
    let (topl, _fl, oil, sigl), (topr, _fr, oir, sigr) =
      EcLowPhlGoal.abstract_info2 env fl fr
    in

    let ml, mr = mleft, mright in
    let bad2 = Fsubst.f_subst_mem mhr mr bad in
    let allinv = f_ands [bad2; invP; invQ] in
    let fvl = PV.fv env ml allinv in
    let fvr = PV.fv env mr allinv in

    PV.check_depend env fvl topl;
    PV.check_depend env fvr topr;

    (* FIXME: check there is only global variable *)
    let eqglob = f_eqglob topl ml topr mr in

    let ospec o_l o_r =
      check_oracle_use pf env topl o_l;
      if   EcPath.x_equal o_l o_r
      then check_oracle_use pf env topl o_r;

      let fo_l = EcEnv.Fun.by_xpath o_l env in
      let fo_r = EcEnv.Fun.by_xpath o_r env in
      let eq_params =
        f_eqparams
          fo_l.f_sig.fs_arg fo_l.f_sig.fs_anames ml
          fo_r.f_sig.fs_arg fo_r.f_sig.fs_anames mr in

      let eq_res =
        f_eqres fo_l.f_sig.fs_ret ml fo_r.f_sig.fs_ret mr in

      let pre   = EcFol.f_ands [EcFol.f_not bad2; eq_params; invP] in
      let post  = EcFol.f_if_simpl bad2 invQ (f_and eq_res invP) in
      let cond1 = f_equivF pre o_l o_r post in
      let cond2 =
        let q = Fsubst.f_subst_mem ml EcFol.mhr invQ in
          f_forall[(mr, GTmem abstract_mt)]
            (f_imp bad2 (f_bdHoareF q o_l q FHeq f_r1)) in
      let cond3 =
        let q  = Fsubst.f_subst_mem mr EcFol.mhr invQ in
        let bq = f_and bad q in
          f_forall [(ml, GTmem abstract_mt)]
            (f_bdHoareF bq o_r bq FHeq f_r1) in

      [cond1; cond2; cond3]
    in

    let sg = List.map2 ospec (OI.allowed oil) (OI.allowed oir) in
    let sg = List.flatten sg in
    let lossless_a = lossless_hyps env topl fl.x_sub in
    let sg = lossless_a :: sg in

    let eq_params =
      f_eqparams
        sigl.fs_arg sigl.fs_anames ml
        sigr.fs_arg sigr.fs_anames mr in

    let eq_res = f_eqres sigl.fs_ret ml sigr.fs_ret mr in

    let pre  = if OI.is_in oil then [eqglob;invP] else [invP] in
    let pre  = f_if_simpl bad2 invQ (f_ands (eq_params::pre)) in
    let post = f_if_simpl bad2 invQ (f_ands [eq_res;eqglob;invP]) in

    (pre, post, sg)
end

(* -------------------------------------------------------------------- *)
let t_equivF_abs_upto_r bad invP invQ tc =
  let env = FApi.tc1_env tc in
  let ef = tc1_as_equivF tc in
  let pre, post, sg =
    UpToLow.equivF_abs_upto !!tc env ef.ef_fl ef.ef_fr bad invP invQ
  in

  let tactic tc = FApi.xmutate1 tc `FunUpto sg in
  FApi.t_last tactic (EcPhlConseq.t_equivF_conseq pre post tc)

let t_equivF_abs_upto = FApi.t_low3 "equiv-fun-abs-upto" t_equivF_abs_upto_r

(* -------------------------------------------------------------------- *)
module ToCodeLow = struct
  (* ------------------------------------------------------------------ *)
  let to_code env f m =
    let fd = Fun.by_xpath f env in
    let me = EcMemory.empty_local ~witharg:false m in
    let arg_name =
      match fd.f_sig.fs_anames with
      | Some [v] -> v.v_name
      | _        -> arg_symbol in
    let arg = {v_name = arg_name; v_type = fd.f_sig.fs_arg } in
    let res = {v_name = "r"; v_type = fd.f_sig.fs_ret } in
    let me = EcMemory.bindall [arg;res] me in
    let args =
      let arg = e_var (pv_loc arg.v_name) arg.v_type in
      match fd.f_sig.fs_anames with
      | None -> [arg]
      | Some [_] -> [arg]
      | Some params -> List.mapi (fun i v -> e_proj arg i v.v_type) params
    in
    let r = pv_loc res.v_name in
    let i = i_call (Some(LvVar(r, res.v_type)), f, args) in
    let s = stmt [i] in
    (me, s, arg, res, args)
  (* (me, s, r, fd.f_sig.fs_ret, args) *)

  let add_var env vfrom mfrom v me s =
    PVM.add env vfrom mfrom (f_pvar (pv_loc v.v_name) v.v_type (fst me)) s

end

(* -------------------------------------------------------------------- *)

let t_fun_to_code_hoare_r tc =
  let env = FApi.tc1_env tc in
  let hf = tc1_as_hoareF tc in
  let f = hf.hf_f in
  let m, st, a, r, _ = ToCodeLow.to_code env f mhr in
  let spr = ToCodeLow.add_var env pv_arg mhr a m PVM.empty in
  let spo = ToCodeLow.add_var env pv_res mhr r m PVM.empty in
  let pre  = PVM.subst env spr hf.hf_pr in
  let post = PVM.subst env spo hf.hf_po in
  let concl = f_hoareS m pre st post in

  FApi.xmutate1 tc `FunToCode [concl]

(* -------------------------------------------------------------------- *)
(* This is for the proc* tactic, which replaces a statement about `G.f` by
   a statement about `x <$ G.f(args)`. *)
let t_fun_to_code_choare_r tc =
  let env = FApi.tc1_env tc in
  let chf = tc1_as_choareF tc in
  let f = chf.chf_f in
  let m, st, a, r, _ = ToCodeLow.to_code env f mhr in
  let spr = ToCodeLow.add_var env pv_arg mhr a m PVM.empty in
  let spo = ToCodeLow.add_var env pv_res mhr r m PVM.empty in
  let pre  = PVM.subst env spr chf.chf_pr in
  let post = PVM.subst env spo chf.chf_po in
  let concl = f_cHoareS m pre st post chf.chf_co in

  FApi.xmutate1 tc `FunToCode [concl]

(* -------------------------------------------------------------------- *)
let t_fun_to_code_bdhoare_r tc =
  let env = FApi.tc1_env tc in
  let hf = tc1_as_bdhoareF tc in
  let f = hf.bhf_f in
  let m, st, a, r, _ = ToCodeLow.to_code env f mhr in
  let spr = ToCodeLow.add_var env pv_arg mhr a m PVM.empty in
  let spo = ToCodeLow.add_var env pv_res mhr r m PVM.empty in
  let pre  = PVM.subst env spr hf.bhf_pr in
  let post = PVM.subst env spo hf.bhf_po in
  let bd   = PVM.subst env spr hf.bhf_bd in
  let concl = f_bdHoareS m pre st post hf.bhf_cmp bd in
  FApi.xmutate1 tc `FunToCode [concl]

(* -------------------------------------------------------------------- *)
let t_fun_to_code_equiv_r tc =
  let env = FApi.tc1_env tc in
  let ef = tc1_as_equivF tc in
  let (fl,fr) = ef.ef_fl, ef.ef_fr in
  let ml, sl, al, rl, _ = ToCodeLow.to_code env fl mleft in
  let mr, sr, ar, rr, _ = ToCodeLow.to_code env fr mright in
  let spr =
    let s = ToCodeLow.add_var env pv_arg mleft al ml PVM.empty in
    ToCodeLow.add_var env pv_arg mright ar mr s in
  let spo =
    let s = ToCodeLow.add_var env pv_res mleft rl ml PVM.empty in
    ToCodeLow.add_var env pv_res mright rr mr s in
  let pre   = PVM.subst env spr ef.ef_pr in
  let post  = PVM.subst env spo ef.ef_po in
  let concl = f_equivS ml mr pre sl sr post in

  FApi.xmutate1 tc `FunToCode [concl]

let t_fun_to_code_eager_r tc =
  let env = FApi.tc1_env tc in
  let eg = tc1_as_eagerF tc in
  let (fl,fr) = eg.eg_fl, eg.eg_fr in
  let ml, sl, al, rl, _ = ToCodeLow.to_code env fl mleft in
  let mr, sr, ar, rr, _ = ToCodeLow.to_code env fr mright in
  let spr =
    let s = ToCodeLow.add_var env pv_arg mleft al ml PVM.empty in
    ToCodeLow.add_var env pv_arg mright ar mr s in
  let spo =
    let s = ToCodeLow.add_var env pv_res mleft rl ml PVM.empty in
    ToCodeLow.add_var env pv_res mright rr mr s in
  let pre   = PVM.subst env spr eg.eg_pr in
  let post  = PVM.subst env spo eg.eg_po in
  let concl =
    f_equivS ml mr pre (s_seq eg.eg_sl sl) (s_seq sr eg.eg_sr) post in
  FApi.xmutate1 tc `FunToCode [concl]

(* -------------------------------------------------------------------- *)
let t_fun_to_code_hoare   = FApi.t_low0 "hoare-fun-to-code"   t_fun_to_code_hoare_r
let t_fun_to_code_choare  = FApi.t_low0 "choare-fun-to-code"  t_fun_to_code_choare_r
let t_fun_to_code_bdhoare = FApi.t_low0 "bdhoare-fun-to-code" t_fun_to_code_bdhoare_r
let t_fun_to_code_equiv   = FApi.t_low0 "equiv-fun-to-code"   t_fun_to_code_equiv_r
let t_fun_to_code_eager   = FApi.t_low0 "eager-fun-to-code"   t_fun_to_code_eager_r


(* -------------------------------------------------------------------- *)
let t_fun_to_code_r tc =
  let th  = t_fun_to_code_hoare in
  let tch = t_fun_to_code_choare in
  let tbh = t_fun_to_code_bdhoare in
  let te  = t_fun_to_code_equiv in
  let teg = t_fun_to_code_eager in
  t_hF_or_chF_or_bhF_or_eF ~th ~tch ~tbh ~te ~teg tc

let t_fun_to_code = FApi.t_low0 "fun-to-code" t_fun_to_code_r

(* -------------------------------------------------------------------- *)
let proj_std a = match a with
  | `Std b -> b
  | _ -> assert false

let proj_costabs a = match a with
  | None -> ([],[])
  | Some (`CostAbs b) -> b
  | _ -> assert false

let t_fun_r inv inv_inf tc =
  let th tc =
    assert (inv_inf = None);
    let env = FApi.tc1_env tc in
    let h   = destr_hoareF (FApi.tc1_goal tc) in
      if   NormMp.is_abstract_fun h.hf_f env
      then t_hoareF_abs inv tc
      else t_hoareF_fun_def tc

  and tch tc =
    let env = FApi.tc1_env tc in
    let h   = destr_cHoareF (FApi.tc1_goal tc) in
    if   NormMp.is_abstract_fun h.chf_f env
    then t_choareF_abs inv (proj_costabs inv_inf) tc
    else begin
      t_choareF_fun_def tc end

  and tbh tc =
    assert (inv_inf = None);
    let env = FApi.tc1_env tc in
    let h   = destr_bdHoareF (FApi.tc1_goal tc) in
      if   NormMp.is_abstract_fun h.bhf_f env
      then t_bdhoareF_abs inv tc
      else t_bdhoareF_fun_def tc

  and te tc =
    assert (inv_inf = None);
    let env = FApi.tc1_env tc in
    let e   = destr_equivF (FApi.tc1_goal tc) in
      if   NormMp.is_abstract_fun e.ef_fl env
      then t_equivF_abs inv tc
      else t_equivF_fun_def tc

  in
    t_hF_or_chF_or_bhF_or_eF ~th ~tch ~tbh ~te tc

let t_fun = FApi.t_low2 "fun" t_fun_r

(* -------------------------------------------------------------------- *)
type p_upto_info = pformula * pformula * (pformula option)

(* -------------------------------------------------------------------- *)
let process_fun_def tc =
  t_fun_def tc

(* -------------------------------------------------------------------- *)
let process_fun_to_code tc =
  t_fun_to_code_r tc

(* -------------------------------------------------------------------- *)
let process_fun_upto_info (bad, p, q) tc =
  let hyps = FApi.tc1_hyps tc in
  let env' = LDecl.inv_memenv hyps in
  let p    = TTC.pf_process_form !!tc env' tbool p in
  let q    = q |> omap (TTC.pf_process_form !!tc env' tbool) |> odfl f_true in
  let bad  =
    let env' = LDecl.push_active (EcMemory.abstract EcFol.mhr) hyps in
    TTC.pf_process_form !!tc env' tbool bad
  in
    (bad, p, q)

(* -------------------------------------------------------------------- *)
let process_fun_upto info g =
  let (bad, p, q) = process_fun_upto_info info g in
    t_equivF_abs_upto bad p q g

(* -------------------------------------------------------------------- *)
let ensure_none tc = function
  | None -> ()
  | Some _ ->
    tc_error !!tc "this is not a choare judgement"

let process_fun_abs inv p_abs_inv_inf tc =
  let t_hoare tc =
    ensure_none tc p_abs_inv_inf;
    let hyps = FApi.tc1_hyps tc in
    let env' = LDecl.inv_memenv1 hyps in
    let inv  = TTC.pf_process_form !!tc env' tbool inv in
    t_hoareF_abs inv tc

  and t_choare tc =
    if p_abs_inv_inf = None then
      tc_error !!tc "for calls to abstract procedures in choare judgements, \
                     additional information must be provided";
    let hyps = FApi.tc1_hyps tc in
    let env' = LDecl.inv_memenv1 hyps in
    let inv  = TTC.pf_process_form !!tc env' tbool inv in
    let abs_inv_info = process_p_abs_inv_inf tc env' (oget p_abs_inv_inf) in
    t_choareF_abs inv abs_inv_info tc

  and t_bdhoare tc =
    ensure_none tc p_abs_inv_inf;
    let hyps = FApi.tc1_hyps tc in
    let env' = LDecl.inv_memenv1 hyps in
    let inv  = TTC.pf_process_form !!tc env' tbool inv in
    t_bdhoareF_abs inv tc

  and t_equiv tc =
    ensure_none tc p_abs_inv_inf;
    let hyps = FApi.tc1_hyps tc in
    let env' = LDecl.inv_memenv hyps in
    let inv  = TTC.pf_process_form !!tc env' tbool inv in
    t_equivF_abs inv tc

  in
  t_hF_or_chF_or_bhF_or_eF
    ~th:t_hoare ~tch:t_choare ~tbh:t_bdhoare ~te:t_equiv tc
