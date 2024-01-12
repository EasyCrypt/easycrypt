(* -------------------------------------------------------------------- *)
open EcParsetree
open EcAst
open EcCoreGoal
open EcModules
open EcFol

(* -------------------------------------------------------------------- *)
let get_expression_of_instruction (i : instr) =
  match i.i_node with
  | Sasgn (lv, e) -> (e, (fun e -> i_asgn (lv, e)))
  | Srnd  (lv, e) -> (e, (fun e -> i_rnd  (lv, e)))
  | _             -> assert false

(* -------------------------------------------------------------------- *)
let process_change
    (side : side option)
    (pos  : pcodepos)
    (form : pformula)
    (tc   : tcenv1)
=
  let env, _, concl = FApi.tc1_eflat tc in

  let change (i : instr) =
    let (e, mk) = get_expression_of_instruction i in
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

  let m, s = EcLowPhlGoal.tc1_get_stmt_with_memory side tc in
  let pos =
    let env = EcEnv.Memory.push_active m env in    
    EcTyping.trans_codepos env pos
  in
  let goals, s = EcMatching.Zipper.map env pos change s in
  let concl = EcLowPhlGoal.hl_set_stmt side concl s in

  FApi.xmutate1 tc `ProcChange (goals @ [concl])

(* -------------------------------------------------------------------- *)
let process_rewrite
    (side : side option)
    (pos  : pcodepos)
    (pt   : ppterm)
    (tc   : tcenv1)
=
  let env, hyps, concl = FApi.tc1_eflat tc in
  let ptenv = EcProofTerm.ptenv_of_penv hyps !!tc in
  let pt = EcProofTerm.process_full_pterm ptenv pt in

  let pts = EcHiGoal.LowRewrite.find_rewrite_patterns `LtoR pt in

  let change (i : instr) =
    let e, mk = get_expression_of_instruction i in
    let e = form_of_expr mhr e in

    let try1 (pt, _, (f1, f2)) =
      let subf, occmode =
        EcProofTerm.pf_find_occurence_lazy pt.EcProofTerm.ptev_env ~ptn:f1 e in

      let f2 = EcProofTerm.concretize_form pt.EcProofTerm.ptev_env f2 in
      let cpos =
        EcMatching.FPosition.select_form
          ~xconv:`AlphaEq ~keyed:occmode.k_keyed
          hyps None subf e in

      let e = EcMatching.FPosition.map cpos (fun _ -> f2) e in

      Some e in

    let e = Option.get (List.find_map try1 pts) in
    ([], [mk (expr_of_form mhr e)])
  in

  let kinds = [`Hoare `Stmt; `EHoare `Stmt; `PHoare `Stmt; `Equiv `Stmt] in

  if not (EcLowPhlGoal.is_program_logic concl kinds) then
    assert false;

  let m, s = EcLowPhlGoal.tc1_get_stmt_with_memory side tc in
  let pos =
    let env = EcEnv.Memory.push_active m env in
    EcTyping.trans_codepos env pos
  in
  let goals, s = EcMatching.Zipper.map env pos change s in
  let concl = EcLowPhlGoal.hl_set_stmt side concl s in

  FApi.xmutate1 tc `ProcRewrite (goals @ [concl])
