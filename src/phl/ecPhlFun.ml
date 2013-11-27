(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcPath
open EcTypes
open EcFol
open EcModules
open EcEnv
open EcBaseLogic
open EcLogic
open EcCorePhl
open EcCoreHiLogic
open EcPV

(* FIXME: oracles should ensure they preserve the state of the adversaries
 *
 * Two solutions:
 *   - add the equalities in the pre and post.
 *   - ensure that oracle doesn't write the adversaries states
 *
 * See [ospec] in [equivF_abs_spec / equivF_abs_upto]
 *)

(* -------------------------------------------------------------------- *)
class rn_hl_fun_def =
object
  inherit xrule "[hl] fun-def"
end

class rn_hl_fun_abs (phi : form) =
object
  inherit xrule "[hl] fun-abs"

  method phi : form = phi
end

class rn_hl_fun_code =
object
  inherit xrule "[hl] fun-code"
end

class rn_hl_fun_upto bad inv1 inv2 =
object
  inherit xrule "[hl] fun-upto"

  method bad  : form = bad
  method inv1 : form = inv1
  method inv2 : form = inv2
end

(* -------------------------------------------------------------------- *)
let rn_hl_fun_def   = RN_xtd (new rn_hl_fun_def   :> xrule)
let rn_hl_fun_abs f = RN_xtd (new rn_hl_fun_abs f :> xrule)
let rn_hl_fun_code  = RN_xtd (new rn_hl_fun_code  :> xrule)

let rn_hl_fun_upto bad inv1 inv2 =
  RN_xtd (new rn_hl_fun_upto bad inv1 inv2 :> xrule)

(* -------------------------------------------------------------------- *)
let check_oracle_use env adv o =
  let use = NormMp.fun_use env o in
  let pp ppe fmt o =
    Format.fprintf fmt "The function %a" (EcPrinting.pp_funname ppe) o
  in
    gen_check_restr env pp o use (Sx.empty, Sm.singleton adv)

let check_concrete env f =
  if NormMp.is_abstract_fun f env then
    let ppe = EcPrinting.PPEnv.ofenv env in
    tacuerror "The function %a is abstract, it should be concrete"
      (EcPrinting.pp_funname ppe) f

(* -------------------------------------------------------------------- *)
let lossless_hyps env top sub =
  let sig_ = (EcEnv.Mod.by_mpath top env).me_sig in
  let bd =
    List.map
      (fun (id, mt) -> (id, GTmodty (mt, (Sx.empty, Sm.singleton top))))
      sig_.mis_params
  in
  (* Warning this implies that the oracle do not have access to top *)
  let args = List.map (fun (id,_) -> EcPath.mident id) sig_.mis_params in
  let concl =
    f_losslessF (EcPath.xpath (EcPath.m_apply top args) sub) in
  let calls =
    let name = EcPath.basename sub in
    let Tys_function (_, oi) =
      oget (List.findopt
        (fun (Tys_function(fs,_)) -> fs.fs_name = name)
        sig_.mis_body)
    in
    oi.oi_calls
  in
  let hyps = List.map f_losslessF calls in
    f_forall bd (f_imps hyps concl)

(* -------------------------------------------------------------------- *)
module FunDefLow = struct
  let t_hoareF_fun_def g =
    let env,_,concl = get_goal_e g in
    let hf = t_as_hoareF concl in
    let f = NormMp.norm_xfun env hf.hf_f in
    check_concrete env f;
    let memenv, fdef, env = Fun.hoareS f env in
    let m = EcMemory.memory memenv in
    let fres =
      match fdef.f_ret with
      | None -> f_tt
      | Some e -> form_of_expr m e in
    let post = PVM.subst1 env (pv_res f) m fres hf.hf_po in
    let concl' = f_hoareS memenv hf.hf_pr fdef.f_body post in
    prove_goal_by [concl'] rn_hl_fun_def g

  let t_bdHoareF_fun_def g =
    let env,_,concl = get_goal_e g in
    let bhf = t_as_bdHoareF concl in
    let f = NormMp.norm_xfun env bhf.bhf_f in
    check_concrete env f;
    let memenv, fdef, env = Fun.hoareS f env in
    let m = EcMemory.memory memenv in
    let fres =
      match fdef.f_ret with
      | None -> f_tt
      | Some e -> form_of_expr m e in
    let post = PVM.subst1 env (pv_res f) m fres bhf.bhf_po in
    let concl' = f_bdHoareS memenv bhf.bhf_pr fdef.f_body post bhf.bhf_cmp bhf.bhf_bd  in
    prove_goal_by [concl'] rn_hl_fun_def g

  let t_equivF_fun_def g =
    let env,_,concl = get_goal_e g in
    let ef = t_as_equivF concl in
    let fl, fr =
      NormMp.norm_xfun env ef.ef_fl,  NormMp.norm_xfun env ef.ef_fr in
    check_concrete env fl; check_concrete env fr;
    let memenvl,fdefl,memenvr,fdefr,env = Fun.equivS fl fr env in
    let ml, mr = EcMemory.memory memenvl, EcMemory.memory memenvr in
    let fresl =
      match fdefl.f_ret with
      | None -> f_tt
      | Some e -> form_of_expr ml e in
    let fresr =
      match fdefr.f_ret with
      | None -> f_tt
      | Some e -> form_of_expr mr e in
    let s = PVM.add env (pv_res fl) ml fresl PVM.empty in
    let s = PVM.add env (pv_res fr) mr fresr s in
    let post = PVM.subst env s ef.ef_po in
    let concl' =
      f_equivS memenvl memenvr ef.ef_pr fdefl.f_body fdefr.f_body post
    in
      prove_goal_by [concl'] rn_hl_fun_def g
end

let t_fun_def g =
  let th  = FunDefLow.t_hoareF_fun_def
  and tbh = FunDefLow.t_bdHoareF_fun_def
  and te  = FunDefLow.t_equivF_fun_def in
    t_hF_or_bhF_or_eF ~th ~tbh ~te g

(* -------------------------------------------------------------------- *)
module FunAbsLow = struct
  let hoareF_abs_spec env f inv =
    let (top, _, oi, _) = abstract_info env f in
    let m = mhr in
    let fv = PV.fv env m inv in
    PV.check_depend env fv top;
    let ospec o = f_hoareF inv o inv in
    let sg = List.map ospec oi.oi_calls in
      (inv, inv, sg)

  let t_hoareF_abs inv g =
    let env,_,concl = get_goal_e g in
    let hf = t_as_hoareF concl in
    let pre, post, sg = hoareF_abs_spec env hf.hf_f inv in
    let tac g' = prove_goal_by sg (rn_hl_fun_abs inv) g' in
      t_on_last tac (EcPhlConseq.t_hoareF_conseq pre post g)

  let equivF_abs_spec env fl fr inv =
    let (topl, fl, oil, sigl) ,
        (topr, fr, oir, sigr) = abstract_info2 env fl fr in
    let ml, mr = mleft, mright in
    let fvl = PV.fv env ml inv in
    let fvr = PV.fv env mr inv in
    PV.check_depend env fvl topl;
    PV.check_depend env fvr topr;
    let eqglob = f_eqglob topl ml topr mr in

    let ospec o_l o_r =
      let use =
        try
          if EcPath.x_equal o_l o_r then check_oracle_use env topl o_l
          else (check_oracle_use env topl o_l;check_oracle_use env topl o_r);
          false
        with e -> if oil.oi_in then true else raise e in
      let fo_l = EcEnv.Fun.by_xpath o_l env in
      let fo_r = EcEnv.Fun.by_xpath o_r env in
      let eq_params =
        f_eqparams o_l fo_l.f_sig.fs_params ml o_r fo_r.f_sig.fs_params mr in
      let eq_res = f_eqres o_l fo_l.f_sig.fs_ret ml o_r fo_r.f_sig.fs_ret mr in
      let invs = if use then [eqglob;inv] else [inv] in
      let pre = EcFol.f_ands (eq_params :: invs) in
      let post = EcFol.f_ands (eq_res :: invs) in
      f_equivF pre o_l o_r post in
    let sg = List.map2 ospec oil.oi_calls oir.oi_calls in
    let eq_params =
      f_eqparams fl sigl.fs_params ml fr sigr.fs_params mr in
    let eq_res = f_eqres fl sigl.fs_ret ml fr sigr.fs_ret mr in
    let lpre = if oil.oi_in then [eqglob;inv] else [inv] in
    let pre = f_ands (eq_params::lpre) in
    let post = f_ands [eq_res; eqglob; inv] in
      (pre, post, sg)

  let t_equivF_abs inv g =
    let env,_,concl = get_goal_e g in
    let ef = t_as_equivF concl in
    let pre, post, sg = equivF_abs_spec env ef.ef_fl ef.ef_fr inv in
    let tac g' = prove_goal_by sg (rn_hl_fun_abs inv) g' in
      t_on_last tac (EcPhlConseq.t_equivF_conseq pre post g)

  let bdHoareF_abs_spec env f inv =
    let top,_,oi,_fsig = abstract_info env f in
    let m = mhr in
    let fv = PV.fv env m inv in
    PV.check_depend env fv top;
    let ospec o =
      ignore (check_oracle_use env top o);
      f_bdHoareF inv o inv FHeq f_r1 in
    let sg = List.map ospec oi.oi_calls in
      (inv, inv, lossless_hyps env top f.x_sub :: sg)

  let t_bdHoareF_abs inv g =
    let env,_,concl = get_goal_e g in
    let bhf = t_as_bdHoareF concl in
    match bhf.bhf_cmp with
    | FHeq when f_equal bhf.bhf_bd f_r1 ->
        let pre, post, sg = bdHoareF_abs_spec env bhf.bhf_f inv in
        let tac g' = prove_goal_by sg (rn_hl_fun_abs inv) g' in
        t_on_last tac (EcPhlConseq.t_bdHoareF_conseq pre post g)
    | _ -> cannot_apply "fun" "expected \"= 1\" as bound"
end

(* -------------------------------------------------------------------- *)
module UpToLow = struct
  let equivF_abs_upto env fl fr bad invP invQ =
    let (topl, fl, oil, sigl) ,
        (topr, fr, oir, sigr) = abstract_info2 env fl fr in
    let ml, mr = mleft, mright in
    let bad2 = Fsubst.f_subst_mem mhr mr bad in
    let allinv = f_ands [bad2; invP; invQ] in
    let fvl = PV.fv env ml allinv in
    let fvr = PV.fv env mr allinv in
    PV.check_depend env fvl topl;
    PV.check_depend env fvr topr;
    (* TODO check there is only global variable *)
    let eqglob = f_eqglob topl ml topr mr in

    let ospec o_l o_r =
      if EcPath.x_equal o_l o_r then check_oracle_use env topl o_l
      else (check_oracle_use env topl o_l;check_oracle_use env topl o_r);
      let fo_l = EcEnv.Fun.by_xpath o_l env in
      let fo_r = EcEnv.Fun.by_xpath o_r env in
      let eq_params =
        f_eqparams o_l fo_l.f_sig.fs_params ml o_r fo_r.f_sig.fs_params mr in
      let eq_res = f_eqres o_l fo_l.f_sig.fs_ret ml o_r fo_r.f_sig.fs_ret mr in
      let pre = EcFol.f_ands [EcFol.f_not bad2; eq_params; invP] in
      let post = EcFol.f_if_simpl bad2 invQ (f_and eq_res invP) in
      let cond1 = f_equivF pre o_l o_r post in
        let cond2 =
        let q = Fsubst.f_subst_mem ml EcFol.mhr invQ in
        f_forall [mr,GTmem None] (f_imp bad2 (f_bdHoareF q o_l q FHeq f_r1)) in
      let cond3 =
        let q = Fsubst.f_subst_mem mr EcFol.mhr invQ in
        let bq = f_and bad q in
        f_forall [ml,GTmem None] (f_bdHoareF bq o_r bq FHeq f_r1) in
      [cond1;cond2;cond3] in
    let sg = List.map2 ospec oil.oi_calls oir.oi_calls in
    let sg = List.flatten sg in
    let lossless_a = lossless_hyps env topl fl.x_sub in
    let sg = lossless_a :: sg in
    let eq_params =
      f_eqparams fl sigl.fs_params ml fr sigr.fs_params mr in
    let eq_res = f_eqres fl sigl.fs_ret ml fr sigr.fs_ret mr in
    let lpre = if oil.oi_in then [eqglob;invP] else [invP] in
    let pre = f_if_simpl bad2 invQ (f_ands (eq_params::lpre)) in
    let post = f_if_simpl bad2 invQ (f_ands [eq_res;eqglob;invP]) in
      (pre, post, sg)

  let t_equivF_abs_upto bad invP invQ g =
    let env,_,concl = get_goal_e g in
    let ef = t_as_equivF concl in
    let pre, post, sg =
      equivF_abs_upto env ef.ef_fl ef.ef_fr bad invP invQ in
    let tac g' = prove_goal_by sg (rn_hl_fun_upto bad invP invQ) g' in
      t_on_last tac (EcPhlConseq.t_equivF_conseq pre post g)
end

(* -------------------------------------------------------------------- *)
let t_fun_to_code g =
  let env, _, concl = get_goal_e g in
  let ef = t_as_equivF concl in
  let (ml,mr), _ = Fun.equivF_memenv ef.ef_fl ef.ef_fr env in
  let fl,fr = ef.ef_fl, ef.ef_fr in
  let do1 f m =
    let fd = Fun.by_xpath f env in
    let args =
      List.map (fun v -> e_var (pv_loc f v.v_name) v.v_type)
        fd.f_sig.fs_params in
    let m, res = fresh_pv m {v_name = "r"; v_type = fd.f_sig.fs_ret} in
    let r = pv_loc f res in
    let i = i_call (Some(LvVar(r,fd.f_sig.fs_ret)), f, args) in
    let s = stmt [i] in
      (m, s, r, fd.f_sig.fs_ret) in
  let ml, sl, rl, tyl = do1 fl ml in
  let mr, sr, rr, tyr = do1 fr mr in
  let s = PVM.add env (pv_res fl) (fst ml) (f_pvar rl tyl (fst ml)) PVM.empty in
  let s = PVM.add env (pv_res fr) (fst mr) (f_pvar rr tyr (fst mr)) s in
  let post = PVM.subst env s ef.ef_po in
  let concl = f_equivS ml mr ef.ef_pr sl sr post in
    (* TODO change the name of the rule *)
    prove_goal_by [concl] rn_hl_fun_code g

(* -------------------------------------------------------------------- *)
let t_fun inv g =
  let th g =
    let env = proj3_1 (get_goal_e g) in
    let h   = destr_hoareF (get_concl g) in
      if   NormMp.is_abstract_fun h.hf_f env
      then FunAbsLow.t_hoareF_abs inv g
      else FunDefLow.t_hoareF_fun_def g
  and tbh g =
    let env = proj3_1 (get_goal_e g) in
    let h   = destr_bdHoareF (get_concl g) in
      if   NormMp.is_abstract_fun h.bhf_f env
      then FunAbsLow.t_bdHoareF_abs inv g
      else FunDefLow.t_bdHoareF_fun_def g
  and te g =
    let env = proj3_1 (get_goal_e g) in
    let e   = destr_equivF (get_concl g) in
      if   NormMp.is_abstract_fun e.ef_fl env
      then FunAbsLow.t_equivF_abs inv g
      else FunDefLow.t_equivF_fun_def g
  in
    t_hF_or_bhF_or_eF ~th ~tbh ~te g

(* -------------------------------------------------------------------- *)
type p_upto_info = pformula * pformula * (pformula option)

let process_fun_upto_info (bad, p, o) g =
  let hyps = get_hyps g in
  let env' = LDecl.inv_memenv hyps in
  let p = process_form env' p tbool in
  let q =
    match o with
    | None -> EcFol.f_true
    | Some q -> process_form env' q tbool in
  let bad =
    let env' = LDecl.push_active (EcFol.mhr, None) hyps in
      process_form env' bad tbool
  in
    (bad, p, q)

let process_fun_upto info g =
  let (bad, p, q) = process_fun_upto_info info g in
    UpToLow.t_equivF_abs_upto bad p q g

let process_fun_abs inv g =
  let hyps,concl = get_goal g in
  if is_equivF concl then
    let env' = LDecl.inv_memenv hyps in
    let inv  = process_form env' inv tbool in
      FunAbsLow.t_equivF_abs inv g
  else
    let env' = LDecl.inv_memenv1 hyps in
    let inv  = process_form env' inv tbool in
      match concl.f_node with
      | FbdHoareF _ -> FunAbsLow.t_bdHoareF_abs inv g
      | FhoareF   _ -> FunAbsLow.t_hoareF_abs   inv g
      | _ -> cannot_apply "fun" "equiv or prob. hoare triple expected"
