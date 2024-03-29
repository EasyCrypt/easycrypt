(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcPath
open EcAst
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
        "The function %a is abstract. Provide an invariant to the [proc] tactic"
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
  let fresh ov =
    match ov.ov_name with
    | None   -> assert false;
    | Some v -> { v_name = v; v_type = ov.ov_type }
  in
  let v = List.map (fun v -> f_pvloc (fresh v) m) fs.fs_anames in
  PVM.add env pv_arg m (f_tuple v) s

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
let t_ehoareF_fun_def_r tc =
  let env = FApi.tc1_env tc in
  let hf = tc1_as_ehoareF tc in
  let f = NormMp.norm_xfun env hf.ehf_f in
  check_concrete !!tc env f;
  let (memenv, (fsig, fdef), env) = Fun.hoareS f env in
  let m = EcMemory.memory memenv in
  let fres  = odfl f_tt (omap (form_of_expr m) fdef.f_ret) in
  let post  = PVM.subst1 env pv_res m fres hf.ehf_po in
  let pre   = PVM.subst env (subst_pre env fsig m PVM.empty) hf.ehf_pr in
  let concl' = f_eHoareS memenv pre fdef.f_body post in
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
let t_ehoareF_fun_def  = FApi.t_low0 "ehoare-fun-def"  t_ehoareF_fun_def_r
let t_bdhoareF_fun_def = FApi.t_low0 "bdhoare-fun-def" t_bdhoareF_fun_def_r
let t_equivF_fun_def   = FApi.t_low0 "equiv-fun-def"   t_equivF_fun_def_r

(* -------------------------------------------------------------------- *)
let t_fun_def_r tc =
  let th  = t_hoareF_fun_def
  and teh = t_ehoareF_fun_def
  and tbh = t_bdhoareF_fun_def
  and te  = t_equivF_fun_def in

  t_hF_or_bhF_or_eF ~th ~teh ~tbh ~te tc

let t_fun_def = FApi.t_low0 "fun-def" t_fun_def_r

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
  let ehoareF_abs_spec _pf env f inv =
    let (top, _, oi, _) = EcLowPhlGoal.abstract_info env f in
    let fv = PV.fv env mhr inv in
    PV.check_depend env fv top;
    let ospec o = f_eHoareF inv o inv in
    let sg = List.map ospec (OI.allowed oi) in
    (inv, inv, sg)

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
        with _ -> true
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
    let lpre   = [eqglob;inv] in
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

let t_ehoareF_abs_r inv tc =
  let env = FApi.tc1_env tc in
  let hf = tc1_as_ehoareF tc in
  let pre, post, sg = FunAbsLow.ehoareF_abs_spec !!tc env hf.ehf_f inv in

  let tactic tc = FApi.xmutate1 tc `FunAbs sg in
  FApi.t_last tactic (EcPhlConseq.t_ehoareF_conseq pre post tc)

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
let t_ehoareF_abs  = FApi.t_low1 "ehoare-fun-abs"  t_ehoareF_abs_r
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

    let pre  = [eqglob;invP] in
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

    let args =
      let freshen_arg i ov =
        match ov.ov_name with
        | None   -> { ov with ov_name = Some (Printf.sprintf "arg%d" (i + 1)) }
        | Some _ -> ov
      in List.mapi freshen_arg fd.f_sig.fs_anames
    in

    let (me, args) = EcMemory.bindall_fresh args me in

    let res = { ov_name = Some "r"; ov_type = fd.f_sig.fs_ret; } in

    let me, res = EcMemory.bind_fresh res me in

    let eargs = List.map (fun v -> e_var (pv_loc (oget v.ov_name)) v.ov_type) args in
    let args =
      let var ov = { v_name = oget ov.ov_name; v_type = ov.ov_type } in
      List.map var args
    in

    let icall =
      i_call (Some (LvVar (pv_loc (oget res.ov_name), res.ov_type)), f, eargs)
    in (me, stmt [icall], res, args)

  let add_var env vfrom mfrom v me s =
    PVM.add env vfrom mfrom (f_pvar (pv_loc (oget v.ov_name)) v.ov_type (fst me)) s

  let add_var_tuple env vfrom mfrom vs me s =
    let vs =
      List.map (fun v -> f_pvar (pv_loc v.v_name) v.v_type (fst me)) vs
    in PVM.add env vfrom mfrom (f_tuple vs) s
end

(* -------------------------------------------------------------------- *)
let t_fun_to_code_hoare_r tc =
  let env = FApi.tc1_env tc in
  let hf = tc1_as_hoareF tc in
  let f = hf.hf_f in
  let m, st, r, a = ToCodeLow.to_code env f mhr in
  let spr = ToCodeLow.add_var_tuple env pv_arg mhr a m PVM.empty in
  let spo = ToCodeLow.add_var env pv_res mhr r m PVM.empty in
  let pre  = PVM.subst env spr hf.hf_pr in
  let post = PVM.subst env spo hf.hf_po in
  let concl = f_hoareS m pre st post in

  FApi.xmutate1 tc `FunToCode [concl]

(* -------------------------------------------------------------------- *)
let t_fun_to_code_ehoare_r tc =
  let env = FApi.tc1_env tc in
  let hf = tc1_as_ehoareF tc in
  let f = hf.ehf_f in
  let m, st, r, a = ToCodeLow.to_code env f mhr in
  let spr = ToCodeLow.add_var_tuple env pv_arg mhr a m PVM.empty in
  let spo = ToCodeLow.add_var env pv_res mhr r m PVM.empty in

  let pre = PVM.subst env spr hf.ehf_pr in

  let post = PVM.subst env spo hf.ehf_po in

  let concl = f_eHoareS m pre st post in

  FApi.xmutate1 tc `FunToCode [concl]

(* -------------------------------------------------------------------- *)
let t_fun_to_code_bdhoare_r tc =
  let env = FApi.tc1_env tc in
  let hf = tc1_as_bdhoareF tc in
  let f = hf.bhf_f in
  let m, st, r, a = ToCodeLow.to_code env f mhr in
  let spr = ToCodeLow.add_var_tuple env pv_arg mhr a m PVM.empty in
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
  let ml, sl, rl, al = ToCodeLow.to_code env fl mleft in
  let mr, sr, rr, ar = ToCodeLow.to_code env fr mright in
  let spr =
    let s = PVM.empty in
    let s = ToCodeLow.add_var_tuple env pv_arg mleft  al ml s in
    let s = ToCodeLow.add_var_tuple env pv_arg mright ar mr s in
    s in
  let spo =
    let s = PVM.empty in
    let s = ToCodeLow.add_var env pv_res mleft  rl ml s in
    let s = ToCodeLow.add_var env pv_res mright rr mr s in
    s in
  let pre   = PVM.subst env spr ef.ef_pr in
  let post  = PVM.subst env spo ef.ef_po in
  let concl = f_equivS ml mr pre sl sr post in

  FApi.xmutate1 tc `FunToCode [concl]

let t_fun_to_code_eager_r tc =
  let env = FApi.tc1_env tc in
  let eg = tc1_as_eagerF tc in
  let (fl,fr) = eg.eg_fl, eg.eg_fr in
  let ml, sl, rl, al = ToCodeLow.to_code env fl mleft in
  let mr, sr, rr, ar = ToCodeLow.to_code env fr mright in
  let spr =
    let s = PVM.empty in
    let s = ToCodeLow.add_var_tuple env pv_arg mleft  al ml s in
    let s = ToCodeLow.add_var_tuple env pv_arg mright ar mr s in
    s in
  let spo =
    let s = PVM.empty in
    let s = ToCodeLow.add_var env pv_res mleft  rl ml s in
    let s = ToCodeLow.add_var env pv_res mright rr mr s in
    s in
  let pre   = PVM.subst env spr eg.eg_pr in
  let post  = PVM.subst env spo eg.eg_po in
  let concl =
    f_equivS ml mr pre (s_seq eg.eg_sl sl) (s_seq sr eg.eg_sr) post in
  FApi.xmutate1 tc `FunToCode [concl]

(* -------------------------------------------------------------------- *)
let t_fun_to_code_hoare   = FApi.t_low0 "hoare-fun-to-code"   t_fun_to_code_hoare_r
let t_fun_to_code_ehoare  = FApi.t_low0 "ehoare-fun-to-code"  t_fun_to_code_ehoare_r
let t_fun_to_code_bdhoare = FApi.t_low0 "bdhoare-fun-to-code" t_fun_to_code_bdhoare_r
let t_fun_to_code_equiv   = FApi.t_low0 "equiv-fun-to-code"   t_fun_to_code_equiv_r
let t_fun_to_code_eager   = FApi.t_low0 "eager-fun-to-code"   t_fun_to_code_eager_r

(* -------------------------------------------------------------------- *)
let t_fun_to_code_r tc =
  let th  = t_fun_to_code_hoare in
  let teh = t_fun_to_code_ehoare in
  let tbh = t_fun_to_code_bdhoare in
  let te  = t_fun_to_code_equiv in
  let teg = t_fun_to_code_eager in
  t_hF_or_bhF_or_eF ~th ~teh ~tbh ~te ~teg tc

let t_fun_to_code = FApi.t_low0 "fun-to-code" t_fun_to_code_r

(* -------------------------------------------------------------------- *)
let t_fun_r inv tc =
  let th tc =
    let env = FApi.tc1_env tc in
    let h   = destr_hoareF (FApi.tc1_goal tc) in
      if   NormMp.is_abstract_fun h.hf_f env
      then t_hoareF_abs inv tc
      else t_hoareF_fun_def tc

  and teh tc =
    let env = FApi.tc1_env tc in
    let h   = destr_eHoareF (FApi.tc1_goal tc) in
      if   NormMp.is_abstract_fun h.ehf_f env
      then t_ehoareF_abs inv tc
      else t_ehoareF_fun_def tc

  and tbh tc =
    let env = FApi.tc1_env tc in
    let h   = destr_bdHoareF (FApi.tc1_goal tc) in
      if   NormMp.is_abstract_fun h.bhf_f env
      then t_bdhoareF_abs inv tc
      else t_bdhoareF_fun_def tc

  and te tc =
    let env = FApi.tc1_env tc in
    let e   = destr_equivF (FApi.tc1_goal tc) in
      if   NormMp.is_abstract_fun e.ef_fl env
      then t_equivF_abs inv tc
      else t_equivF_fun_def tc

  in
    t_hF_or_bhF_or_eF ~th ~teh ~tbh ~te tc

let t_fun = FApi.t_low1 "fun" t_fun_r

(* -------------------------------------------------------------------- *)
type p_upto_info = pformula * pformula * (pformula option)

(* -------------------------------------------------------------------- *)
let process_fun_def tc =
  let t_cont tcenv =
    if FApi.tc_count tcenv = 2 then
      FApi.t_sub [EcLowGoal.t_trivial; EcLowGoal.t_id] tcenv
    else tcenv in
  t_cont (t_fun_def tc)

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
let process_fun_abs inv tc =
  let t_hoare tc =
    let hyps = FApi.tc1_hyps tc in
    let env' = LDecl.inv_memenv1 hyps in
    let inv  = TTC.pf_process_form !!tc env' tbool inv in
    t_hoareF_abs inv tc

  and t_ehoare tc =
    let hyps = FApi.tc1_hyps tc in
    let env' = LDecl.inv_memenv1 hyps in
    let inv  = TTC.pf_process_xreal !!tc env' inv in
    t_ehoareF_abs inv tc

  and t_bdhoare tc =
    let hyps = FApi.tc1_hyps tc in
    let env' = LDecl.inv_memenv1 hyps in
    let inv  = TTC.pf_process_form !!tc env' tbool inv in
    t_bdhoareF_abs inv tc

  and t_equiv tc =
    let hyps = FApi.tc1_hyps tc in
    let env' = LDecl.inv_memenv hyps in
    let inv  = TTC.pf_process_form !!tc env' tbool inv in
    t_equivF_abs inv tc

  in
  t_hF_or_bhF_or_eF ~th:t_hoare ~teh:t_ehoare ~tbh:t_bdhoare ~te:t_equiv tc
