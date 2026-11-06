(* -------------------------------------------------------------------- *)
open EcUtils
open EcAst
open EcParsetree
open EcCoreGoal

module Zpr = EcMatching.Zipper

(* -------------------------------------------------------------------- *)
(* The rw_prgm tactics are derived, hoare only: they resolve their
   arguments, check what they always checked (keeping their error
   messages), and apply a program transformation of the catalogue through
   the hoare transformation rule ([EcHoareTransform]):
   - [proc change circuit]: [EcTrCircuitChange] (the circuit-equivalence
     check is made by the transformation; no obligation);
   - [idassign]: [EcTrIdAssign] (no obligation). *)

(* -------------------------------------------------------------------- *)
type change_t = pcodepos * ptybindings option * int * pstmt

(* -------------------------------------------------------------------- *)
let process_change ((cpos, bindings, i, s) : change_t) (tc : tcenv1) =
  let hyps = FApi.tc1_hyps tc in
  let env = EcEnv.LDecl.toenv hyps in
  let hs = EcLowPhlGoal.tc1_as_hoareS tc in
  let cpos = EcLowPhlGoal.tc1_process_codepos tc (None, cpos) in

  if not (POE.is_empty (hs_po hs).hsi_inv) then
    tc_error !!tc "exceptions not supported";

  let mem, binds =
    let bindings =
      bindings
      |> Option.value ~default:[]
      |> List.map (fun (xs, ty) -> List.map (fun x -> (x, ty)) xs)
      |> List.flatten in
    List.fold_left_map (fun mem (x, ty) ->
      let ue = EcUnify.UniEnv.create (Some (EcEnv.LDecl.tohyps hyps).h_tvar) in
      let ty = EcTyping.transty EcTyping.tp_tydecl env ue ty in
      assert (EcUnify.UniEnv.closed ue);
      let ty = 
        let subst = EcCoreSubst.Tuni.subst (EcUnify.UniEnv.close ue) in
        EcCoreSubst.ty_subst subst ty in
      let x = Option.map EcLocation.unloc (EcLocation.unloc x) in
      let vr = EcAst.{ ov_name = x; ov_type = ty; } in
      let (mem, _) = EcMemory.bind_fresh vr mem in
      if Option.is_none x then
        tc_error !!tc "Missing name for variable";
      (mem, vr)
    ) hs.hs_m bindings in

  let env = EcEnv.Memory.push_active_ss mem env in

  let s =
    let ue = EcProofTyping.unienv_of_hyps (FApi.tc1_hyps tc) in
    let s  = EcTyping.transstmt env ue s in

    if not (EcUnify.UniEnv.closed ue) 
    then tc_error !!tc "Failed to infer all types for type variables"; 

    let sb = EcCoreSubst.Tuni.subst (EcUnify.UniEnv.close ue) in
    EcCoreSubst.s_subst sb s in

  let zp, (at, _) = Zpr.zipper_of_cpos_r env cpos hs.hs_s in

  (* Fails (with [Invalid_argument]) when there are fewer than [i]
     instructions at the position. *)
  ignore (List.split_at i zp.z_tail : _ * _);

  EcHoareTransform.t_hoare_transform
    { htr_tr = EcTrCircuitChange.TrCircuitChange
        { trcc_at = at; trcc_len = i; trcc_binds = binds; trcc_stmt = s; } }
    tc

(* -------------------------------------------------------------------- *)
type idassign_t = pcodepos * pqsymbol

(* -------------------------------------------------------------------- *)
let process_idassign ((cpos, pv) : idassign_t) (tc : tcenv1) =
  let env = FApi.tc1_env tc in
  let hs = EcLowPhlGoal.tc1_as_hoareS tc in
  let env = EcEnv.Memory.push_active_ss hs.hs_m env in

  let cpos = EcTyping.trans_codepos env cpos in
  let pv = EcTyping.trans_pv env pv in
  let _, (at, _) = Zpr.zipper_of_cpos_r env cpos hs.hs_s in

  EcHoareTransform.t_hoare_transform
    { htr_tr = EcTrIdAssign.TrIdAssign { tria_at = at; tria_pv = pv; } }
    tc

(* -------------------------------------------------------------------- *)
let process_rw_prgm (mode : rwprgm) (tc : tcenv1) =
  match mode with
  | `IdAssign (cpos, pv) ->
    process_idassign (cpos, pv) tc
  | `Change (cpos, bindings, i, s) ->
    process_change (cpos, bindings, i, s) tc

