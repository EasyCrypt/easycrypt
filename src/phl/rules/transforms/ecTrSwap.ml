(* -------------------------------------------------------------------- *)
open EcModules
open EcPV
open EcMatching.Position
open EcPlTransform

(* -------------------------------------------------------------------- *)
(* Parameters of the [swap] transformation, resolved: the block to move is
   an integer gap range of the (possibly nested) block at a normalized
   path, and its destination an integer gap of that block. *)
type tr_swap = {
  trsw_range  : nm_codegap_range;
  trsw_target : nm_codegap1;
}

type EcPlTransform.transform += TrSwap of tr_swap

(* -------------------------------------------------------------------- *)
(* The two adjacent statements [s1; s2] can be exchanged: neither raises,
   and neither reads nor writes what the other writes. Swapping two
   independent blocks preserves the final state of the runs that
   terminate normally, but not the state in which an exception is
   raised: if one of the blocks raises, the other one has run (or not)
   before. Hence blocks that contain a [raise] are never swapped, and,
   when the judgement observes exceptions ([exn]), neither are blocks
   that may raise (through a procedure call,
   [EcLowPhlGoal.s_may_raise]). Otherwise, raising is as good as not
   terminating, which the swap preserves. *)
let check_swap ~(exn : bool) (env : EcEnv.env) (s1 : stmt) (s2 : stmt) =
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
    raise (InvalidTransform "cannot swap blocks that contain exceptions");

  if exn && List.exists (EcLowPhlGoal.s_may_raise env) [s1; s2] then
    raise (InvalidTransform
             "cannot swap blocks that may raise an exception \
              (through a procedure call) when the postcondition \
              constrains exceptions");

  let m1,m2 = s_write env s1, s_write env s2 in
  let r1,r2 = s_read  env s1, s_read  env s2 in
  (* FIXME: this is not sufficient *)
  let m2r1 = PV.interdep env m2 r1 in
  let m1m2 = PV.interdep env m1 m2 in
  let m1r2 = PV.interdep env m1 r2 in

  let error mode d =
    let (s1, s2) =
      match mode with
      | `RW -> "reads" , "written"
      | `WR -> "writes", "read"
      | `WW -> "writes", "written"
    in
    raise (InvalidTransform (Format.asprintf
      "the two statements are not independent, %t"
      (fun fmt ->
        Format.fprintf fmt
          "the first statement %s %a which is %s by the second"
          s1 (PV.pp env) d s2)))
  in
    if not (PV.is_empty m2r1) then error `RW m2r1;
    if not (PV.is_empty m1m2) then error `WW m1m2;
    if not (PV.is_empty m1r2) then error `WR m1r2

(* -------------------------------------------------------------------- *)
(* Move the block [c[start..fin)] of the block at [path] to the gap
   [target] of that block, outside of the moved block, checking that it is
   independent of the instructions it is exchanged with. *)
let swap (p : tr_swap) (ctxt : tr_ctxt) (s : stmt) =
  let (path, (start, fin)), target = p.trsw_range, p.trsw_target in
  let zpr =
    try  EcMatching.Zipper.zipper_of_nm_cgap ctxt.trc_env (path, start) s
    with InvalidCPos -> raise (InvalidTransform "invalid range for swap") in
  let env = EcUtils.odfl ctxt.trc_env zpr.z_env in
  let s = stmt (List.rev_append zpr.z_head zpr.z_tail) in

  let gaps =
    if   not (start <= fin && fin <= List.length s.s_node)
    then raise (InvalidTransform "invalid range for swap")
    else if 0 <= target && target <= start then [target; start; fin]
    else if fin <= target && target <= List.length s.s_node then [start; fin; target]
    else raise (InvalidTransform "invalid offset for swap") in

  match split_by_nmcgaps gaps s with
  | [hd; s1; s2; tl] ->
      check_swap ~exn:ctxt.trc_exn env (stmt s1) (stmt s2);
      let s = EcMatching.Zipper.zip
        { zpr with z_head = []; z_tail = List.flatten [hd; s2; s1; tl] } in
      { trr_me = ctxt.trc_me; trr_s = s; trr_obl = []; }
  | _ -> assert false

let () =
  register (function
    | TrSwap p -> Some (swap p)
    | _ -> None)
