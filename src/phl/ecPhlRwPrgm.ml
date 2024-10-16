(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
type change_t = pcodepos * int * pstmt

(* -------------------------------------------------------------------- *)
let process_change ((cpos, i, s) : change_t) (tc : tcenv1) =
  let env = FApi.tc1_env tc in
  let hs = EcLowPhlGoal.tc1_as_hoareS tc in
  let env = EcEnv.Memory.push_active hs.hs_m env in

  let cpos = EcTyping.trans_codepos env cpos in

  let s =
    let ue = EcProofTyping.unienv_of_hyps (FApi.tc1_hyps tc) in
    let s  = EcTyping.transstmt env ue s in

    assert (EcUnify.UniEnv.closed ue); (* FIXME *)

    let sb = EcCoreSubst.Tuni.subst (EcUnify.UniEnv.close ue) in
    EcCoreSubst.s_subst sb s in

  let zp = Zpr.zipper_of_cpos env cpos hs.hs_s in
  let zp =
    let target, tl = List.split_at i zp.z_tail in

    begin
      try
        if not (EcCircuits.instrs_equiv (FApi.tc1_hyps tc) hs.hs_m target s.s_node) then
          tc_error !!tc "statements are not circuit-equivalent"
        with EcCircuits.CircError s ->
          tc_error !!tc "circuit-equivalence checker error: %s" s
    end;
    { zp with z_tail = s.s_node @ tl } in

  let hs = { hs with hs_s = Zpr.zip zp } in

  FApi.xmutate1 tc `BChange [EcFol.f_hoareS_r hs]

(* -------------------------------------------------------------------- *)
type idassign_t = pcodepos * pqsymbol

(* -------------------------------------------------------------------- *)
let process_idassign ((cpos, pv) : idassign_t) (tc : tcenv1) =
  let env = FApi.tc1_env tc in
  let hs = EcLowPhlGoal.tc1_as_hoareS tc in
  let env = EcEnv.Memory.push_active hs.hs_m env in

  let cpos = EcTyping.trans_codepos env cpos in
  let pv, pvty = EcTyping.trans_pv env pv in
  let sasgn = EcModules.i_asgn (LvVar (pv, pvty), EcTypes.e_var pv pvty) in
  let hs =
    let s = Zpr.zipper_of_cpos env cpos hs.hs_s in
    let s = { s with z_tail = sasgn :: s.z_tail } in
    { hs with hs_s = Zpr.zip s } in
  FApi.xmutate1 tc `IdAssign [EcFol.f_hoareS_r hs]

(* -------------------------------------------------------------------- *)
let process_rw_prgm (mode : rwprgm) (tc : tcenv1) =
  match mode with 
  | `IdAssign (cpos, pv) ->
    process_idassign (cpos, pv) tc
  | `Change (cpos, i, s) ->
    process_change (cpos, i, s) tc
