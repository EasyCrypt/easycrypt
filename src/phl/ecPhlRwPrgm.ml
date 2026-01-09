(* -------------------------------------------------------------------- *)
open EcUtils
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
      (mem, (EcTypes.pv_loc (oget x), ty)) (* FIXME *)
    ) hs.hs_m bindings in

  let env = EcEnv.Memory.push_active_ss mem env in

  let s =
    let ue = EcProofTyping.unienv_of_hyps (FApi.tc1_hyps tc) in
    let s  = EcTyping.transstmt env ue s in

    assert (EcUnify.UniEnv.closed ue); (* FIXME *)

    let sb = EcCoreSubst.Tuni.subst (EcUnify.UniEnv.close ue) in
    EcCoreSubst.s_subst sb s in

  let zp = Zpr.zipper_of_cpos env cpos hs.hs_s in

  let rec pvtail (pvs : EcPV.PV.t) (zp : Zpr.ipath) =
    let parent =
      match zp with
      | Zpr.ZTop -> None
      | Zpr.ZWhile (_, p) -> Some p
      | Zpr.ZIfThen (e, p, _) -> Some p
      | Zpr.ZIfElse (e, _, p) -> Some p
      | Zpr.ZMatch (e, p, _) -> Some p in
    match parent with
    | None -> pvs
    | Some ((_, tl), p) -> pvtail (EcPV.PV.union pvs (EcPV.is_read env tl)) p
  in

  let zp =
    let target, tl = List.split_at i zp.z_tail in

    let keep = pvtail (EcPV.is_read env tl) zp.z_path in
    let keep = EcPV.PV.union keep (EcPV.PV.fv env (EcMemory.memory mem) (EcAst.hs_po hs).inv) in

    begin
      try
        if not (EcCircuits.instrs_equiv (FApi.tc1_hyps tc) ~keep mem target s.s_node) then
          tc_error !!tc "statements are not circuit-equivalent"
        with EcCircuits.CircError s ->
          tc_error !!tc "circuit-equivalence checker error: %s" (Lazy.force s)
    end;
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
  FApi.xmutate1 tc `IdAssign EcAst.[EcFol.f_hoareS (hs.hs_m |> snd) (hs_pr hs) (hs.hs_s) (hs_po hs)]

(* -------------------------------------------------------------------- *)
let process_rw_prgm (mode : rwprgm) (tc : tcenv1) =
  match mode with 
  | `IdAssign (cpos, pv) ->
    process_idassign (cpos, pv) tc
  | `Change (cpos, bindings, i, s) ->
    process_change (cpos, bindings, i, s) tc

