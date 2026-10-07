(* -------------------------------------------------------------------- *)
open EcUtils
open EcAst
open EcParsetree
open EcCoreGoal
open EcLowPhlGoal

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

  let mem, _ =
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
      let x = match x with
      | Some x -> x
      | None -> tc_error !!tc "Missing name for variable" 
      in
      (mem, (EcTypes.pv_loc x, ty)) 
    ) hs.hs_m bindings in

  let env = EcEnv.Memory.push_active_ss mem env in

  let s =
    let ue = EcProofTyping.unienv_of_hyps (FApi.tc1_hyps tc) in
    let s  = EcTyping.transstmt env ue s in

    if not (EcUnify.UniEnv.closed ue) 
    then tc_error !!tc "Failed to infer all types for type variables"; 

    let sb = EcCoreSubst.Tuni.subst (EcUnify.UniEnv.close ue) in
    EcCoreSubst.s_subst sb s in

  let zp = Zpr.zipper_of_cpos env cpos hs.hs_s in

  let zp =
    let target, tl = List.split_at i zp.z_tail in

    (* [keep] is the set of variables on which [target] and [s] must
       agree. Let [R] be the variables read by both [target] and [s].
       We take for [keep]:
       - the variables read by the code that may run after the fragment
         (for each enclosing [while], its guard and its whole body),
         and by the postcondition;
       - if the fragment is inside a loop, [R].
       Soundness: the original and the new programs are related by
       "the states agree on [keep]" (they are equal before the first
       run of the fragment). The code that may run after the fragment
       only reads [keep], so preserves this relation. When reaching the
       fragment in states [m1] (original) and [m2] (new), let [m] be
       [m2] updated with the values of [m1] on [read(target) \ R].
       Then [m] agrees with [m1] on [read(target)] and on [keep] (as
       [R] is included in [keep]), and with [m2] on [read(s)] and on
       [keep]. As [target] and [s] are deterministic, we get
       [target(m1) =keep target(m) =keep s(m) =keep s(m2)], the middle
       equality being the one established by the circuit checker.
       Outside a loop, the fragment is run once, from [m1 = m2], and
       [R] does not need to be kept. *)
    let keep =
      let zpr = ((zp.z_head, tl), zp.z_path) in
      EcPV.zpr_pv `Read `After env EcPV.PV.empty zpr in
    let keep =
      if Zpr.in_loop zp.z_path then
        EcPV.PV.union keep
          (EcPV.PV.inter
             (EcPV.is_read env target)
             (EcPV.is_read env s.s_node))
      else keep in
    let keep = EcPV.PV.union keep (EcPV.PV.fv env (EcMemory.memory mem) (POE.lower (EcAst.hs_po hs)).inv) in
    (* The variables that are neither read nor written by [target] and
       [s] are left unchanged by both and need not be compared. This
       drops the global variables, which [target] and [s] cannot access
       (this is checked by the circuit checker). *)
    let keep =
      let ts = target @ s.s_node in
      EcPV.PV.inter keep
        (EcPV.PV.union (EcPV.is_read env ts) (EcPV.is_write env ts)) in
    let st = EcLowCircuits.create_state (EcEnv.gstate env) in

    let equiv =
      try EcCircuits.instrs_equiv (FApi.tc1_hyps tc) ~keep mem st target s.s_node
      with e ->
        tc_error !!tc "circuit-equivalence checker error: %s" (Printexc.to_string e)
    in
    if not equiv then
      tc_error !!tc "statements are not circuit-equivalent";
    { zp with z_tail = s.s_node @ tl } in

  let hs = { hs with hs_s = Zpr.zip zp; hs_m = mem; } in

  FApi.xmutate1 tc `BChange EcAst.[EcFol.f_hoareS (hs.hs_m |> snd) (hs_pr hs) (hs.hs_s) (hs_po hs)]

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
  FApi.xmutate1 tc `IdAssign
    [EcFol.f_hoareS (snd hs.hs_m) (hs_pr hs) (hs.hs_s) (hs_po hs)]

(* -------------------------------------------------------------------- *)
let process_rw_prgm (mode : rwprgm) (tc : tcenv1) =
  match mode with
  | `IdAssign (cpos, pv) ->
    process_idassign (cpos, pv) tc
  | `Change (cpos, bindings, i, s) ->
    process_change (cpos, bindings, i, s) tc

