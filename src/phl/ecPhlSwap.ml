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
  interval : (codepos1 * codepos1 option) option;
  offset   : codeoffset1;
}

(* -------------------------------------------------------------------- *)
module LowInternal = struct
  let check_swap (pf : proofenv) (env : EcEnv.env) (s1 : stmt) (s2 : stmt) =
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
    let len = List.length s.s_node in

    let p1, p2 (* inclusive *)=
      match info.interval with
      | Some (p , None   ) -> p , p
      | Some (p1, Some p2) -> p1, p2
      | None ->
        let p =
          match info.offset with
          | `ByOffset offset when offset < 0 -> `ByPos (-1)
          | _ -> `ByPos 1 in
        let p : codepos1 = (0, p) in (p, p)
    in

    let process_cpos (p : codepos1) =
      try  EcMatching.Zipper.offset_of_position env p s
      with EcMatching.Zipper.InvalidCPos ->
        tc_error_lazy pf (fun fmt ->
          let ppe = EcPrinting.PPEnv.ofenv env in
          Format.fprintf fmt "invalid position: %a" (EcPrinting.pp_codepos1 ppe) p
        ) in

    let i1 = process_cpos p1 in
    let i2 = process_cpos p2 in

    if i2 < i1 then
      tc_error_lazy pf (fun fmt ->
        let ppe = EcPrinting.PPEnv.ofenv env in
        Format.fprintf fmt
          "invalid/empty code block: [%a..%a] (resolved as [%d..%d])"
          (EcPrinting.pp_codepos1 ppe) p1
          (EcPrinting.pp_codepos1 ppe) p2
          i1 i2
      );

    let offset =
      match info.offset with
      | `ByPosition p ->
        let target = EcMatching.Zipper.offset_of_position env p s in
        if i1 < target && target <= i2 then
          tc_error_lazy pf (fun fmt ->
            let ppe = EcPrinting.PPEnv.ofenv env in
            Format.fprintf fmt
              "destination is inside the moved block: %a \\in ]%a..%a] (resolved as %d \\in ]%d..%d])"
              (EcPrinting.pp_codeoffset1 ppe) info.offset
              (EcPrinting.pp_codepos1 ppe) p1
              (EcPrinting.pp_codepos1 ppe) p2
              target i1 i2
          );
        if target <= i1 then target - i1 else target - i2 - 1

      | `ByOffset o ->
        o
    in

    let target = if 0 <= offset then i2+offset+1 else i1+offset in

    if target <= 0 then
      tc_error_lazy pf (fun fmt ->
        let ppe = EcPrinting.PPEnv.ofenv env in
        Format.fprintf fmt
          "offset (%d) is too small by %d: start index is %a (resolved to %d)"
          offset (1 + abs target) (EcPrinting.pp_codepos1 ppe) p1 i1
      );

    if target > len+1 then
      tc_error_lazy pf (fun fmt ->
        let ppe = EcPrinting.PPEnv.ofenv env in
        Format.fprintf fmt
          "offset (%d) is too larget by %d: end index is %a (resolved to %d)"
          offset (target - len - 1) (EcPrinting.pp_codepos1 ppe) p2 i2
      );

    let b1, b2, b3 =
      if target <= i1 then target, i1, i2+1 else i1, i2+1, target in

    let hd , tl = List.takedrop (b1-1 ) s.s_node in
    let s12, tl = List.takedrop (b2-b1) tl in
    let s23, tl = List.takedrop (b3-b2) tl in

    check_swap pf env (stmt s12) (stmt s23);
    stmt (List.flatten [hd; s23; s12; tl])
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
    let env = FApi.tc1_env tc in
    let me, _ = EcLowPhlGoal.tc1_get_stmt side tc in

    let process_codepos =
      let env = EcEnv.Memory.push_active_ss me env in
      fun p -> EcTyping.trans_codepos1 env p in

    let process_codeoffset (o : pcodeoffset1) : codeoffset1 =
        match o with
        | `ByOffset   i -> `ByOffset i
        | `ByPosition p -> `ByPosition (process_codepos p) in

    let interval =
      Option.map (fun (p1, p2) ->
        let p1 = process_codepos p1 in
        let p2 = Option.map process_codepos p2 in
        (p1, p2)
      ) pos.interval in

    let offset = process_codeoffset pos.offset in

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

    let rec aux pos1 pos2 k tc =
      if k <= 0 then t_id tc else
        let data : pswap_kind =
          let p1 = (0, `ByPos pos2) in
          let p2 = (0, `ByPos (pos2+n2-1)) in
          let o  = `ByOffset ((pos1+n1) - pos2) in
          { interval = Some (p1, Some p2); offset = o; } in
        FApi.t_seq
          (process_swap1 (mk_loc loc (side, data)))
          (aux (pos1+n1+n2) (pos2+n2) (k-1))
        tc in

    FApi.t_seq (aux pos1 pos2 k) (aux_list (pos1, n1 + n2) lpos2) tc

  in aux_list pos_n1 lpos2 tc
