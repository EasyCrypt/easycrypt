(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcLocation
open EcAst
open EcModules
open EcFol
open EcPV
open EcMatching.Position
open EcCoreGoal
open EcLowGoal

(* -------------------------------------------------------------------- *)
type swap_kind = {
  interval : codegap_range;
  offset   : codegap_offset1;
}

(* -------------------------------------------------------------------- *)
module LowInternal = struct
  let check_swap (pf : proofenv) (env : EcEnv.env) (s1 : stmt) (s2 : stmt) =
    let is_contains_raise =
      let exception HasRaise in

      let rec i_contains_raise (i : instr) =
        match i.i_node with
        | Sraise _ -> raise HasRaise
        | _ -> EcModules.i_iter i_contains_raise i in

      fun (s : stmt) ->
        try
          List.iter i_contains_raise s.s_node;
          false
        with HasRaise -> true in

    if List.exists is_contains_raise [s1; s2] then
      tc_error pf "cannot swap blocks that contain exceptions";

    let m1,m2 = s_write env s1, s_write env s2 in
    let r1,r2 = s_read  env s1, s_read  env s2 in
    (* FIXME: this is not sufficient *)
    let m2r1 = PV.interdep env m2 r1 in
    let m1m2 = PV.interdep env m1 m2 in
    let m1r2 = PV.interdep env m1 r2 in

    let error mode d =
      tc_error_lazy pf (fun fmt ->
        Format.fprintf fmt
          "the two statements are not independent, %t"
          (fun fmt ->
            let (s1, s2) =
              match mode with
              | `RW -> "reads" , "written"
              | `WR -> "writes", "read"
              | `WW -> "writes", "written"
            in
              Format.fprintf fmt
                "the first statement %s %a which is %s by the second"
                s1 (PV.pp env) d s2))
    in
      if not (PV.is_empty m2r1) then error `RW m2r1;
      if not (PV.is_empty m1m2) then error `WW m1m2;
      if not (PV.is_empty m1r2) then error `WR m1r2


  let swap_stmt
    (pf   : proofenv   )
    (env  : EcEnv.env  )
    (info : swap_kind  )
    (s    : stmt       )
  =
    let (env, s), (_, (start, fin)) = try 
      let (cpath, (start, fin)) = info.interval in
      normalize_cgap_range env (cpath, (start, fin)) s 
    with InvalidCPos ->
      tc_error_lazy pf (fun fmt ->
        let ppe = EcPrinting.PPEnv.ofenv env in
        Format.fprintf fmt "invalid range: %a" (EcPrinting.pp_codegap_range ppe) info.interval
      )
    in

    let target = try
      resolve_gap_offset env (start, fin) info.offset s
    with InvalidCPos ->
      tc_error pf "invalid offset for swap"
    in

    match split_by_nmcgaps
      (if target <= start
      then [target; start; fin]
      else [start; fin; target]
      ) s
    with 
    | [hd; s1; s2; tl] -> check_swap pf env (stmt s1) (stmt s2);
      stmt (List.flatten [hd; s2; s1; tl])
    | _ -> assert false
end

(* -------------------------------------------------------------------- *)
let t_swap_r (side : oside) (info : swap_kind) (tc : tcenv1) =
  let env = FApi.tc1_env tc in
  let _, stmt = EcLowPhlGoal.tc1_get_stmt side tc in
  let stmt = LowInternal.swap_stmt !!tc env info stmt in
  FApi.xmutate1 tc `Swap [EcLowPhlGoal.hl_set_stmt side (FApi.tc1_goal tc) stmt]

(* -------------------------------------------------------------------- *)
let t_swap = FApi.t_low2 "swap" t_swap_r

(* -------------------------------------------------------------------- *)
let rec process_swap1 (info : (oside * pswap_kind) located) (tc : tcenv1) =
  let side, pos = info.pl_desc in
  let concl = FApi.tc1_goal tc in

  if is_equivS concl && Option.is_none side then
    FApi.t_seq
      (process_swap1 { info with pl_desc = (Some `Left , pos)})
      (process_swap1 { info with pl_desc = (Some `Right, pos)})
      tc
  else
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
