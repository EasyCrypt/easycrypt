(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal
open EcLowPhlGoal
open EcAst

(* -------------------------------------------------------------------- *)
type change_t = pcodepos * ptybindings option * int * pstmt

(* -------------------------------------------------------------------- *)
type idassign_t = pcodepos * pqsymbol

(* -------------------------------------------------------------------- *)
let process_idassign ((cpos, pv) : idassign_t) (tc : tcenv1) =
  let env = FApi.tc1_env tc in
  let hs = EcLowPhlGoal.tc1_as_hoareS tc in
  let env = EcEnv.Memory.push_active_ss hs.hs_m env in

  let cpos = EcTyping.trans_codepos env cpos in
  let pv, pvty = EcTyping.trans_pv env pv in
  let sasgn = EcModules.i_asgn (LvVar (pv, pvty), EcTypes.e_var pv pvty) in
  let hs =
    let s = Zpr.zipper_of_cpos env cpos hs.hs_s in
    let s = { s with z_tail = sasgn :: s.z_tail } in
    { hs with hs_s = Zpr.zip s } in
  FApi.xmutate1 tc `IdAssign [EcFol.f_hoareS (snd hs.hs_m) (hs_pr hs) (hs.hs_s) (hs_po hs)]

(* -------------------------------------------------------------------- *)
let process_rw_prgm (mode : rwprgm) (tc : tcenv1) =
  match mode with 
  | `IdAssign (cpos, pv) ->
    process_idassign (cpos, pv) tc
