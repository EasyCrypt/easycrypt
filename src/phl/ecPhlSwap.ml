(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2017 - Inria
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcLocation
open EcModules
open EcFol
open EcPV

open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
module LowInternal = struct
  let check_swap tc s1 s2 =
    let env = FApi.tc1_env tc in

    let m1,m2 = s_write env s1, s_write env s2 in
    let r1,r2 = s_read  env s1, s_read  env s2 in
    (* FIXME: this is not sufficient *)
    let m2r1 = PV.interdep env m2 r1 in
    let m1m2 = PV.interdep env m1 m2 in
    let m1r2 = PV.interdep env m1 r2 in

    let error mode d =
      tc_error_lazy !!tc (fun fmt ->
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

  let swap_stmt tc p1 p2 p3 s =
    let s   = s.s_node in
    let len = List.length s in
    if not (1 <= p1 && p1 < p2 && p2 <= p3 && p3 <= len) then
      tc_error_lazy !!tc (fun fmt ->
        Format.fprintf fmt
          "invalid position, 1 <= %i < %i <= %i <= %i"
          p1 p2 p3 len);
    let hd ,tl = List.takedrop (p1-1) s in
    let s12,tl = List.takedrop (p2-p1) tl in
    let s23,tl = List.takedrop (p3-p2+1) tl in
      check_swap tc (stmt s12) (stmt s23);
      stmt (List.flatten [hd;s23;s12;tl])
end

(* -------------------------------------------------------------------- *)
let t_hoare_swap_r p1 p2 p3 tc =
  let hs    = tc1_as_hoareS tc in
  let s     = LowInternal.swap_stmt tc p1 p2 p3 hs.hs_s in
  let concl = f_hoareS_r { hs with hs_s = s } in
  FApi.xmutate1 tc `Swap [concl]

(* -------------------------------------------------------------------- *)
let t_bdhoare_swap_r p1 p2 p3 tc =
  let bhs   = tc1_as_bdhoareS tc in
  let s     = LowInternal.swap_stmt tc p1 p2 p3 bhs.bhs_s in
  let concl = f_bdHoareS_r {bhs with bhs_s = s } in
  FApi.xmutate1 tc `Swap [concl]

(* -------------------------------------------------------------------- *)
let t_equiv_swap_r side p1 p2 p3 tc =
  let es    = tc1_as_equivS tc in
  let sl,sr =
    match side with
    | `Left  -> LowInternal.swap_stmt tc p1 p2 p3 es.es_sl, es.es_sr
    | `Right -> es.es_sl, LowInternal.swap_stmt tc p1 p2 p3 es.es_sr
  in
  let concl = f_equivS_r { es with es_sl = sl; es_sr = sr; } in
  FApi.xmutate1 tc `Swap [concl]

(* -------------------------------------------------------------------- *)
let t_hoare_swap   = FApi.t_low3 "hoare-swap"   t_hoare_swap_r
let t_bdhoare_swap = FApi.t_low3 "bdhoare-swap" t_bdhoare_swap_r
let t_equiv_swap   = FApi.t_low4 "equiv-swap"   t_equiv_swap_r

(* -------------------------------------------------------------------- *)
module HiInternal = struct
  let stmt_length side tc =
    match (FApi.tc1_goal tc).f_node, side with
    | FhoareS hs   , None -> List.length hs.hs_s.s_node
    | FbdHoareS bhs, None -> List.length bhs.bhs_s.s_node

    | FequivS es, Some `Left  -> List.length es.es_sl.s_node
    | FequivS es, Some `Right -> List.length es.es_sr.s_node

    | _, None   -> tc_error_noXhl ~kinds:[`Hoare `Stmt; `PHoare `Stmt] !!tc
    | _, Some _ -> tc_error_noXhl ~kinds:[`Equiv `Stmt] !!tc
end

(* -------------------------------------------------------------------- *)
let rec process_swap1 info tc =
  let side, pos = info.pl_desc in
  let concl     = FApi.tc1_goal tc in

  if is_equivS concl && side = None then
    FApi.t_seq
      (process_swap1 { info with pl_desc = (Some `Left , pos)})
      (process_swap1 { info with pl_desc = (Some `Right, pos)})
      tc
  else
    let p1, p2, p3 = match pos with
      | SKbase (p1, p2, p3) ->
          (p1, p2, p3)

      | SKmove p ->
          let forneg () =
            let len = HiInternal.stmt_length side tc in
              (len+p, len, len)
          in
               if 0 < p then (1, 2, p+1)
          else if p < 0 then forneg ()
          else (* p = 0 *)   (0, 0, 0)

      | SKmovei (i, p) ->
               if 0 < p then (i, i+1, i+p)
          else if p < 0 then (i+p, i, i)
          else (* p = 0 *)   (0, 0, 0)

      | SKmoveinter (i1, i2, p) ->
               if 0 < p then (i1, i2+1, i2+p)
          else if p < 0 then (i1+p, i1, i2)
          else (* p = 0 *)   (0, 0, 0)

    in

    let tactic =
      if p1 = 0 then t_id else
        match side with
        | None when is_hoareS concl ->
            t_hoare_swap p1 p2 p3
        | None when is_bdHoareS concl ->
            t_bdhoare_swap p1 p2 p3
        | None ->
            FApi.t_seq
              (process_swap1 { info with pl_desc = (Some `Left , pos)})
              (process_swap1 { info with pl_desc = (Some `Right, pos)})
        | Some side ->
            t_equiv_swap side p1 p2 p3
    in
      EcCoreGoal.reloc info.pl_loc tactic tc

(* -------------------------------------------------------------------- *)
let process_swap info tc =
  FApi.t_seqs (List.map process_swap1 info) tc
