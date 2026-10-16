(* -------------------------------------------------------------------- *)
open EcAst
open EcFol
open EcEnv

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* The [proc] rules live, one module per (logic, rule), in
   [rules/<logic>/]: [Ec<Logic>FunDef] (a concrete procedure, by its body),
   [Ec<Logic>FunAbs] (an abstract procedure, with an invariant),
   [EcEquivFunAbsUpto] (an abstract procedure, up to a bad event) and
   [Ec<Logic>FunToCode] ([proc*]); their shared computations are in
   [EcPlFun]. This module only keeps the legacy entry points (adapters
   onto those rules, so external callers and this module's interface are
   unchanged) and the logic-agnostic dispatchers. *)

(* -------------------------------------------------------------------- *)
let check_concrete = EcPlFun.check_concrete
let subst_pre      = EcPlFun.subst_pre

(* -------------------------------------------------------------------- *)
let t_hoareF_fun_def   = EcHoareFunDef.t_hoareF_fun_def
let t_bdhoareF_fun_def = EcBdHoareFunDef.t_bdhoareF_fun_def
let t_equivF_fun_def   = EcEquivFunDef.t_equivF_fun_def

let t_fun_def tc =
  let th  = t_hoareF_fun_def
  and teh = EcEHoareFunDef.t_ehoareF_fun_def
  and tbh = t_bdhoareF_fun_def
  and te  = t_equivF_fun_def in

  t_hF_or_bhF_or_eF ~th ~teh ~tbh ~te tc

(* -------------------------------------------------------------------- *)
module FunAbsLow = struct
  let hoareF_abs_spec (_ : proofenv) env f inv =
    EcHoareFunAbs.hoareF_abs_spec env f inv

  let bdhoareF_abs_spec (_ : proofenv) env f inv =
    EcBdHoareFunAbs.bdhoareF_abs_spec env f inv

  let equivF_abs_spec (_ : proofenv) env fl fr inv =
    EcEquivFunAbs.equivF_abs_spec env fl fr inv
end

(* -------------------------------------------------------------------- *)
let t_hoareF_abs inv =
  EcHoareFunAbs.(t_hoareF_abs_full { hfa_inv = inv })

let t_ehoareF_abs inv =
  EcEHoareFunAbs.(t_ehoareF_abs_full { ehfa_inv = inv })

let t_bdhoareF_abs inv =
  EcBdHoareFunAbs.(t_bdhoareF_abs_full { bhfa_inv = inv })

let t_equivF_abs inv =
  EcEquivFunAbs.(t_equivF_abs_full { efa_inv = inv })

(* -------------------------------------------------------------------- *)
let t_equivF_abs_upto weakened_pre bad invP invQ =
  EcEquivFunAbsUpto.(t_equivF_abs_upto_full
    { efu_ll   = Option.value ~default:false weakened_pre;
      efu_bad  = bad;
      efu_inv  = invP;
      efu_binv = invQ; })

(* -------------------------------------------------------------------- *)
let t_fun_to_code tc =
  let th  = EcHoareFunToCode.t_hoareF_fun_to_code in
  let teh = EcEHoareFunToCode.t_ehoareF_fun_to_code in
  let tbh = EcBdHoareFunToCode.t_bdhoareF_fun_to_code in
  let te  = EcEquivFunToCode.t_equivF_fun_to_code in
  let teg = EcEagerFunToCode.t_eagerF_fun_to_code in
  t_hF_or_bhF_or_eF ~th ~teh ~tbh ~te ~teg tc

(* -------------------------------------------------------------------- *)
let t_fun (inv: inv) tc =
  let th tc =
    let inv = match inv with
      | Inv_ss inv -> inv
      | _ -> tc_error !!tc "expected a single sided invariant" in
    let env = FApi.tc1_env tc in
    let h   = destr_hoareF (FApi.tc1_goal tc) in
      if   NormMp.is_abstract_fun h.hf_f env
      then t_hoareF_abs inv tc
      else t_hoareF_fun_def tc

  and teh tc =
    let inv = match inv with
      | Inv_ss inv -> inv
      |  _ -> tc_error !!tc "expected a single sided invariant" in
    let env = FApi.tc1_env tc in
    let h   = destr_eHoareF (FApi.tc1_goal tc) in
      if   NormMp.is_abstract_fun h.ehf_f env
      then t_ehoareF_abs inv tc
      else EcEHoareFunDef.t_ehoareF_fun_def tc

  and tbh tc =
    let inv = match inv with
      | Inv_ss inv -> inv
      |  _ -> tc_error !!tc "expected a single sided invariant" in
    let env = FApi.tc1_env tc in
    let h   = destr_bdHoareF (FApi.tc1_goal tc) in
      if   NormMp.is_abstract_fun h.bhf_f env
      then t_bdhoareF_abs inv tc
      else t_bdhoareF_fun_def tc

  and te tc =
    let inv = match inv with
      | Inv_ts inv -> inv
      | _ -> tc_error !!tc "expected a two sided invariant" in
    let env = FApi.tc1_env tc in
    let e   = destr_equivF (FApi.tc1_goal tc) in
      if   NormMp.is_abstract_fun e.ef_fl env
      then t_equivF_abs inv tc
      else t_equivF_fun_def tc

  in
    t_hF_or_bhF_or_eF ~th ~teh ~tbh ~te tc

(* -------------------------------------------------------------------- *)
let process_fun_def tc =
  let t_cont tcenv =
    if FApi.tc_count tcenv = 2 then
      FApi.t_sub [EcLowGoal.t_trivial; EcLowGoal.t_id] tcenv
    else tcenv in
  t_cont (t_fun_def tc)

(* -------------------------------------------------------------------- *)
let process_fun_to_code tc =
  t_fun_to_code tc

(* -------------------------------------------------------------------- *)
let process_fun_upto_info (info : EcParsetree.fun_upto_info) tc =
  let r = EcEquivFunAbsUpto.process_equivF_abs_upto_info info tc in
  EcEquivFunAbsUpto.(info.fui_is_ll_variant, r.efu_bad, r.efu_inv, r.efu_binv)

(* -------------------------------------------------------------------- *)
let process_fun_upto info tc =
  EcEquivFunAbsUpto.process_equivF_abs_upto info tc

(* -------------------------------------------------------------------- *)
(* Dispatch on the goal kind only; each logic types the invariant. *)
let process_fun_abs inv tc =
  t_hF_or_bhF_or_eF
    ~th:(EcHoareFunAbs.process_hoareF_abs inv)
    ~teh:(EcEHoareFunAbs.process_ehoareF_abs inv)
    ~tbh:(EcBdHoareFunAbs.process_bdhoareF_abs inv)
    ~te:(EcEquivFunAbs.process_equivF_abs inv)
    tc
