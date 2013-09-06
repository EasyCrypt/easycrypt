(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcTypes
open EcModules
open EcFol
open EcEnv
open EcBaseLogic
open EcLogic
open EcPV
open EcMetaProg
open EcCorePhl
open EcCoreHiPhl

module Zpr = EcMetaProg.Zipper

(* -------------------------------------------------------------------- *)
let check_fission_independence env b init c1 c2 c3 =
  (* TODO improve error message, see swap *)
  let check_disjoint s1 s2 = 
    if not (PV.indep env s1 s2) then
      tacuerror "in loop-fission, independence check failed"
  in

  let fv_b    = e_read   env PV.empty b    in
  let rd_init = is_read  env PV.empty init in
  let wr_init = is_write env PV.empty init in
  let rd_c1   = is_read  env PV.empty c1   in
  let rd_c2   = is_read  env PV.empty c2   in
  let rd_c3   = is_read  env PV.empty c3   in
  let wr_c1   = is_write env PV.empty c1   in
  let wr_c2   = is_write env PV.empty c2   in
  let wr_c3   = is_write env PV.empty c3   in

  check_disjoint rd_c1 wr_c2;
  check_disjoint rd_c2 wr_c1;
  List.iter (check_disjoint fv_b) [wr_c1; wr_c2];
  check_disjoint fv_b (PV.diff wr_c3 wr_init);
  List.iter (check_disjoint rd_init) [wr_init; wr_c1; wr_c3];
  List.iter (check_disjoint rd_c3) [wr_c1; wr_c2]

(* -------------------------------------------------------------------- *)
type fission_t = bool option * codepos * (int * (int * int))

class rn_hl_fission side pos split =
object
  inherit xrule "[hl] loop-fission"

  method side     : bool option       = side
  method position : codepos           = pos
  method split    : int * (int * int) = split
end

let rn_hl_fission side pos split =
  RN_xtd (new rn_hl_fission side pos split :> xrule)

let fission_stmt (il, (d1, d2)) env me zpr =
  if d2 < d1 then
    tacuerror "%s, %s"
      "in loop-fission"
      "second break offset must not be lower than the first one";
  
  let (hd, init, b, sw, tl) =
    match zpr.Zpr.z_tail with
    | { i_node = Swhile (b, sw) } :: tl -> begin
        if List.length zpr.Zpr.z_head < il then
          tacuerror "while-loop is not headed by %d intructions" il;
      let (init, hd) = List.take_n il zpr.Zpr.z_head in
        (hd, init, b, sw, tl)
      end
    | _ -> tacuerror "code position does not lead to a while-loop"
  in

  if d2 > List.length sw.s_node then
    tacuerror "in loop fission, invalid offsets range";

  let (s1, s2, s3) =
    let (s1, s2) = List.take_n (d1   ) sw.s_node in
    let (s2, s3) = List.take_n (d2-d1) s2 in
      (s1, s2, s3)
  in

  check_fission_independence env b init s1 s2 s3;

  let wl1 = i_while (b, stmt (s1 @ s3)) in
  let wl2 = i_while (b, stmt (s2 @ s3)) in
  let fis =   (List.rev_append init [wl1])
            @ (List.rev_append init [wl2]) in

    (me, { zpr with Zpr.z_head = hd; Zpr.z_tail = fis @ tl }, [])

let t_fission side cpos infos g =
  let tr = fun side -> rn_hl_fission side cpos infos in
  let cb = fun hyps _ me zpr -> fission_stmt infos (LDecl.toenv hyps) me zpr in
    t_code_transform side cpos tr (t_zip cb) g

let process_fission (side, cpos, infos) g =
  t_fission side cpos infos g

(* -------------------------------------------------------------------- *)
type fusion_t = bool option * codepos * (int * (int * int))

class rn_hl_fusion side pos split =
object
  inherit xrule "[hl] loop-fusion"

  method side     : bool option       = side
  method position : codepos           = pos
  method split    : int * (int * int) = split
end

let rn_hl_fusion side pos split =
  RN_xtd (new rn_hl_fusion side pos split :> xrule)

let fusion_stmt (il, (d1, d2)) env me zpr =
  let (hd, init1, b1, sw1, tl) =
    match zpr.Zpr.z_tail with
    | { i_node = Swhile (b, sw) } :: tl -> begin
        if List.length zpr.Zpr.z_head < il then
          tacuerror "1st while-loop is not headed by %d intruction(s)" il;
      let (init, hd) = List.take_n il zpr.Zpr.z_head in
        (hd, init, b, sw, tl)
      end
    | _ -> tacuerror "code position does not lead to a while-loop"
  in

  let (init2, b2, sw2, tl) =
    if List.length tl < il then
      tacuerror "1st first-loop is not followed by %d instruction(s)" il;
    let (init2, tl) = List.take_n il tl in
      match tl with
      | { i_node = Swhile (b2, sw2) } :: tl -> (List.rev init2, b2, sw2, tl)
      | _ -> tacuerror "cannot find the 2nd while-loop"
  in

  if d1 > List.length sw1.s_node then
    tacuerror "in loop-fusion, body is less than %d instruction(s)" d1;
  if d2 > List.length sw2.s_node then
    tacuerror "in loop-fusion, body is less than %d instruction(s)" d2;

  let (sw1, fini1) = List.take_n d1 sw1.s_node in
  let (sw2, fini2) = List.take_n d2 sw2.s_node in

  (* FIXME: costly *)
  if not (EcReduction.s_equal_norm env (stmt init1) (stmt init2)) then
    tacuerror "in loop-fusion, preludes do not match";
  if not (EcReduction.s_equal_norm env (stmt fini1) (stmt fini2)) then
    tacuerror "in loop-fusion, finalizers do not match";
  if not (EcReduction.e_equal_norm env b1 b2) then
    tacuerror "in loop-fusion, while conditions do not match";

  check_fission_independence env b1 init1 sw1 sw2 fini1;

  let wl  = i_while (b1, stmt (sw1 @ sw2 @ fini1)) in
  let fus = List.rev_append init1 [wl] in

    (me, { zpr with Zpr.z_head = hd; Zpr.z_tail = fus @ tl; }, [])

let t_fusion side cpos infos g =
  let tr = fun side -> rn_hl_fusion side cpos infos in
  let cb = fun hyps _ me zpr -> fusion_stmt infos (LDecl.toenv hyps) me zpr in
    t_code_transform side cpos tr (t_zip cb) g

let process_fusion (side, cpos, infos) g =
  t_fusion side cpos infos g

(* -------------------------------------------------------------------- *)
type unroll_t = bool option * EcParsetree.codepos

class rn_hl_unroll side pos =
object
  inherit xrule "[hl] loop-unroll"

  method side     : bool option = side
  method position : codepos     = pos
end

let rn_hl_unroll side pos =
  RN_xtd (new rn_hl_unroll side pos :> xrule)

let unroll_stmt _ me i =
  match i.i_node with
  | Swhile (e, sw) -> (me, [i_if (e, sw, stmt []); i])
  | _ -> tacuerror "cannot find a while loop at given position"

let t_unroll side cpos g =
  let tr = fun side -> rn_hl_unroll side cpos in
    t_code_transform side cpos tr (t_fold unroll_stmt) g

let process_unroll (side, cpos) g =
  t_unroll side cpos g

(* -------------------------------------------------------------------- *)
type splitwhile_t = pexpr * bool option * codepos

class rn_hl_splitwhile cond side pos =
object
  inherit xrule "[hl] split-while"

  method condition : expr        = cond
  method side      : bool option = side
  method position  : codepos     = pos
end

let rn_hl_splitwhile cond side pos =
  RN_xtd (new rn_hl_splitwhile cond side pos :> xrule)

let splitwhile_stmt b _env me i =
  match i.i_node with
  | Swhile (e, sw) -> 
      let op_and = e_op EcCoreLib.p_and [] (tfun tbool (tfun tbool tbool)) in
      let e = e_app op_and [e; b] tbool in
        (me, [i_while (e, sw); i])

  | _ -> tacuerror "cannot find a while loop at given position"

let t_splitwhile b side cpos g =
  let tr = fun side -> rn_hl_splitwhile b side cpos in
    t_code_transform side cpos tr (t_fold (splitwhile_stmt b)) g

let process_splitwhile (b, side, cpos) g =
  let b = process_phl_exp side b tbool g in
    t_splitwhile b side cpos g
