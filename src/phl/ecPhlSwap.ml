(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcLocation
open EcAst
open EcModules
open EcMatching.Position
open EcCoreGoal
open EcLowGoal

(* -------------------------------------------------------------------- *)
type swap_kind = {
  interval : codegap_range;
  offset   : codegap_offset1;
}

(* -------------------------------------------------------------------- *)
(* [swap] is derived in every logic: the positions are resolved here
   (failing as before the migration when they are invalid), then the
   [swap] program transformation ([EcTrSwap], which checks the
   independence of the exchanged statements) is applied through the
   transformation rule of the logic. The derived tactic is the same in
   every logic, hence a single dispatcher on the goal kind. *)
let resolve_swap (pf : proofenv) (env : EcEnv.env) (info : swap_kind) (s : stmt) =
  let zpr, _, (path, (start, fin)) = try
    EcMatching.Zipper.zipper_and_split_of_cgap_range env info.interval s
  with InvalidCPos ->
    tc_error_lazy pf (fun fmt ->
      let ppe = EcPrinting.PPEnv.ofenv env in
      Format.fprintf fmt "invalid range: %a" (EcPrinting.pp_codegap_range ppe) info.interval
    )
  in

  let env = odfl env zpr.z_env in
  let s = stmt (List.rev_append zpr.z_head zpr.z_tail) in

  let target = try
    resolve_gap_offset env (start, fin) info.offset s
  with InvalidCPos ->
    tc_error pf "invalid offset for swap"
  in

  EcTrSwap.TrSwap { trsw_range = (path, (start, fin)); trsw_target = target; }

(* -------------------------------------------------------------------- *)
let t_swap (side : oside) (info : swap_kind) (tc : tcenv1) =
  let _, s = EcLowPhlGoal.tc1_get_stmt side tc in
  let tr = resolve_swap !!tc (FApi.tc1_env tc) info s in
  match side, (FApi.tc1_goal tc).f_node with
  | None, FhoareS _ ->
      EcHoareTransform.t_hoare_transform { htr_tr = tr } tc
  | None, FeHoareS _ ->
      EcEHoareTransform.t_ehoare_transform { ehtr_tr = tr } tc
  | None, FbdHoareS _ ->
      EcBdHoareTransform.t_bdhoare_transform { btr_tr = tr } tc
  | Some side, FequivS _ ->
      EcEquivTransform.t_equiv_transform { etr_side = side; etr_tr = tr } tc
  | _ -> assert false

(* -------------------------------------------------------------------- *)
let rec process_swap1 (info : (oside * pswap_kind) located) (tc : tcenv1) =
  let side, pos = info.pl_desc in
  let concl = FApi.tc1_goal tc in

  match side, concl.f_node with
  | None, FequivS _ ->
    FApi.t_seq
      (process_swap1 { info with pl_desc = (Some `Left , pos)})
      (process_swap1 { info with pl_desc = (Some `Right, pos)})
      tc
  | _ ->
    let me, _ = EcLowPhlGoal.tc1_get_stmt side tc in
    let env = EcEnv.Memory.push_active_ss me (FApi.tc1_env tc) in

    let interval =
      Option.map (fun pcpor ->
        EcTyping.trans_codepos_or_range ~memory:(fst me) env pcpor
      ) pos.interval in

    let offset = EcTyping.trans_codegap_offset1 ~memory:(fst me) env pos.offset in

    let interval = match interval, offset with
    | Some interval, _ -> interval
    | None, GapRelative i ->
        codegap_range_of_codepos
        (if i > 0 then cpos_first else cpos_last)
    | None, _ ->
      tc_error (!!tc) "Cannot give a absolute offset and no range"
    in
      

    let kind : swap_kind = { interval; offset } in

    EcCoreGoal.reloc info.pl_loc (t_swap side kind) tc

(* -------------------------------------------------------------------- *)
let process_swap info tc =
  FApi.t_seqs (List.map process_swap1 info) tc

(* -------------------------------------------------------------------- *)
let process_interleave info tc =
  let loc = info.pl_loc in
  let (side, pos_n1, lpos2, k) = info.pl_desc in

  let rec aux_list (pos1, n1) lpos2 tc =
    match lpos2 with [] -> t_id tc | (pos2, n2) :: lpos2 ->

    if not (pos1 + k * n1 <= pos2) then
      tc_error !!tc
        "invalide interleave range (%i + %i * %i <= %i)"
        pos1 k n1 pos2;

    (* FIXME: should use t_swap and not process_swap; offset should use gap type *)
    let rec aux pos1 pos2 k tc =
      if k <= 0 then t_id tc else
        let data : pswap_kind =
          (* Represent range [pos2, pos2+n2[ *)
          let p1 = (0, `ByPos (pos2, `Index1)) in
          let p2 = (0, `ByPos (pos2+n2, `Index1)) in
          let o  = PGapRelative ((pos1+n1) - pos2) in
          { interval = Some (Range ([], (GapBefore p1, GapBefore p2))); offset = o; } in
        FApi.t_seq
          (process_swap1 (mk_loc loc (side, data)))
          (aux (pos1+n1+n2) (pos2+n2) (k-1))
        tc in

    FApi.t_seq (aux pos1 pos2 k) (aux_list (pos1, n1 + n2) lpos2) tc

  in aux_list pos_n1 lpos2 tc
