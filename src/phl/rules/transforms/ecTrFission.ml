(* -------------------------------------------------------------------- *)
open EcUtils
open EcAst
open EcModules
open EcPV
open EcPlTransform

module Zpr = EcMatching.Zipper

(* -------------------------------------------------------------------- *)
(* Parameters of the [fission] transformation, resolved: the position of
   the loop is a normalized (possibly nested) code position. *)
type tr_fission = {
  trfi_at   : EcMatching.Position.nm_codepos;
  trfi_init : int;
  trfi_d1   : int;
  trfi_d2   : int;
}

type EcPlTransform.transform += TrFission of tr_fission

(* -------------------------------------------------------------------- *)
(* Side conditions of loop fission / fusion, which state:

     init; while b { c1; c2; c3 }
       ==  init; while b { c1; c3 }; init; while b { c2; c3 }

   (1) [init] (prelude) and [c3] (epilog) are deterministic, loop-,
       call- and exception-free ([check_dslc]), and [c1] / [c2] do not
       raise exceptions ([check_noraise]);
   (2) [b] and [c3] read nothing written by [c1] or [c2];
   (3) [c1] and [c2] commute: neither reads what the other writes, and
       they write disjoint sets of variables;
   (4) [c3] only writes variables that [init] writes;
   (5) [init] reads nothing written by [init], [c1] or [c3], and writes
       nothing written by [c1].

   Soundness: by (1) and (2), the number of iterations and the values
   taken by the variables written by [c3] are a function of the state
   after [init]. Then, by (2) and (3), in the fused loop, the [c1] part
   (on [wr c1]) and the [c2; c3] part (on the other variables) evolve
   without any information flow between them: the fused loop has the
   same distribution as the product of the two split loops. By (1),
   (4) and (5), the second [init] restores the state after the first
   one on all variables but [wr c1], which it leaves untouched. Since
   this is an equivalence, the same conditions apply to fusion. *)
let check_independence env b init c1 c2 c3 =
  (* TODO improve error message, see swap *)
  let check_disjoint s1 s2 =
    if not (PV.indep env s1 s2) then
      raise (InvalidTransform "independence check failed")
  in

  let fv_b    = e_read   env b    in
  let rd_init = is_read  env init in
  let wr_init = is_write env init in
  let rd_c1   = is_read  env c1   in
  let rd_c2   = is_read  env c2   in
  let rd_c3   = is_read  env c3   in
  let wr_c1   = is_write env c1   in
  let wr_c2   = is_write env c2   in
  let wr_c3   = is_write env c3   in

  check_disjoint rd_c1 wr_c2;
  check_disjoint rd_c2 wr_c1;
  check_disjoint wr_c1 wr_c2;
  List.iter (check_disjoint fv_b) [wr_c1; wr_c2];
  if not (PV.subset wr_c3 wr_init) then
    raise (InvalidTransform
             "epilog must only write variables written by the prelude");
  List.iter (check_disjoint rd_init) [wr_init; wr_c1; wr_c3];
  check_disjoint wr_init wr_c1;
  List.iter (check_disjoint rd_c3) [wr_c1; wr_c2]

(* -------------------------------------------------------------------- *)
let check_dslc name =
  let error () =
    raise (InvalidTransform
             (Printf.sprintf
                "%s must be deterministic and loop/procedure-call free" name)) in

  let rec doit_i c =
    match c.i_node with
    | Sasgn _ ->
       ()

    | Sif (_, c1, c2) ->
       List.iter doit_s [c1; c2]

    | Smatch (_, bs) ->
       List.iter (doit_s -| snd) bs

    | Srnd _ | Scall _ | Swhile _ | Sraise _  | Sabstract _ ->
       error ()

  and doit_s c =
    List.iter doit_i c.s_node

  in fun c -> List.iter doit_i c

(* -------------------------------------------------------------------- *)
(* [c1] / [c2] must not raise: if one raises at some iteration, the
   executions of the other one that precede it in the original loop are
   lost (or added). A [raise] is always rejected; when the judgement
   observes exceptions ([exn], see [EcTrSwap]), so is a call to a
   procedure that may raise ([EcLowPhlGoal.s_may_raise]). Otherwise,
   raising is as good as not terminating, which fission / fusion
   preserve. *)
let check_noraise ~(exn : bool) env =
  let rec doit_i c =
    match c.i_node with
    | Sraise _ ->
        raise (InvalidTransform "loop body must not raise exceptions")
    | _ -> EcModules.i_iter doit_i c

  in fun c ->
    List.iter doit_i c;
    if exn && EcLowPhlGoal.s_may_raise env (stmt c) then
      raise (InvalidTransform
               "loop body must not call procedures that may raise \
                exceptions when the postcondition constrains exceptions")

(* All the side conditions, on the prelude [init], the condition [b], the
   two parts [c1], [c2] and the epilog [c3]. *)
let check_side_conditions ~exn env b init c1 c2 c3 =
  check_independence env b init c1 c2 c3;
  check_dslc "prelude" init;
  check_dslc "epilog" c3;
  List.iter (check_noraise ~exn env) [c1; c2]

(* -------------------------------------------------------------------- *)
(* Split the loop at [p], headed by [n] instructions, at the offsets
   [d1 <= d2] of its body. *)
let fission (p : tr_fission) (ctxt : tr_ctxt) (s : stmt) =
  let il, d1, d2 = p.trfi_init, p.trfi_d1, p.trfi_d2 in
  let error msg = raise (InvalidTransform msg) in

  let zpr =
    let cpos = EcMatching.Position.cpos_of_nm_cpos p.trfi_at in
    try  Zpr.zipper_of_cpos ctxt.trc_env cpos s
    with EcMatching.Position.InvalidCPos -> error "invalid code position" in

  if d2 < d1 then
    error (Printf.sprintf "%s, %s"
             "in loop-fission"
             "second break offset must not be lower than the first one");

  let (hd, init, b, sw, tl) =
    match zpr.Zpr.z_tail with
    | { i_node = Swhile (b, sw) } :: tl -> begin
        if List.length zpr.Zpr.z_head < il then
          error (Printf.sprintf
                   "while-loop is not headed by %d intructions" il);
      let (init, hd) = List.takedrop il zpr.Zpr.z_head in
        (hd, init, b, sw, tl)
      end
    | _ -> error "code position does not lead to a while-loop"
  in

  if d2 > List.length sw.s_node then
    error "in loop fission, invalid offsets range";

  let (s1, s2, s3) =
    let (s1, s2) = List.takedrop (d1   ) sw.s_node in
    let (s2, s3) = List.takedrop (d2-d1) s2 in
      (s1, s2, s3)
  in

  check_side_conditions ~exn:ctxt.trc_exn ctxt.trc_env b init s1 s2 s3;

  let wl1 = i_while (b, stmt (s1 @ s3)) in
  let wl2 = i_while (b, stmt (s2 @ s3)) in
  let fis =   (List.rev_append init [wl1])
            @ (List.rev_append init [wl2]) in

  { trr_me  = ctxt.trc_me;
    trr_s   = Zpr.zip { zpr with Zpr.z_head = hd; Zpr.z_tail = fis @ tl };
    trr_obl = []; }

let () =
  register (function
    | TrFission p -> Some (fission p)
    | _ -> None)
