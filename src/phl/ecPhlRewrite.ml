(* -------------------------------------------------------------------- *)
open EcParsetree
open EcAst
open EcCoreGoal
open EcModules
open EcFol

(* -------------------------------------------------------------------- *)
let process_change
    (side : side option)
    (pos  : codepos)
    (form : pformula)
    (tc   : tcenv1)
=
  let concl = FApi.tc1_goal tc in

  let change i =
    let (e, mk) =
      match i.i_node with
      | Sasgn (lv, e) -> (e, (fun e -> i_asgn (lv, e)))
      | Srnd  (lv, e) -> (e, (fun e -> i_rnd  (lv, e)))
      | _             -> assert false in

    let m, e' = EcProofTyping.tc1_process_Xhl_form ?side tc e.e_ty form in
    let mid = EcMemory.memory m in
    let e' = expr_of_form mid e' in

    let f  = form_of_expr mid e in
    let f' = form_of_expr mid e' in

    ([f_forall_mems [m] (f_eq f f')], [mk e'])
  in

  let kinds = [`Hoare `Stmt; `EHoare `Stmt; `PHoare `Stmt; `Equiv `Stmt] in

  if not (EcLowPhlGoal.is_program_logic concl kinds) then
    assert false;

  let s = EcLowPhlGoal.tc1_get_stmt side tc in
  let goals, s = EcMatching.Zipper.map pos change s in
  let concl = EcLowPhlGoal.hl_set_stmt side concl s in

  FApi.xmutate1 tc `ProcChange (goals @ [concl])
