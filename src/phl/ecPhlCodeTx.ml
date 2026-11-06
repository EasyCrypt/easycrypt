(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcAst
open EcModules
open EcFol
open EcEnv
open EcPV
open EcMatching

open EcCoreGoal
open EcLowPhlGoal

module Mid = EcIdent.Mid
module Zpr = EcMatching.Zipper
module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
(* The code transformations (kill, alias, set, set-match, cfold, the split
   of a tuple assignment and simplify-if) are derived, uniformly in every
   logic: they resolve their code position (and their other arguments),
   check what they always checked (keeping their error messages), and
   apply a program transformation of the catalogue ([EcTrKill],
   [EcTrAlias], [EcTrSet], [EcTrSetMatch], [EcTrCFold], [EcTrAsgnCase],
   [EcTrSimplifyIf]) through the transformation rule of the logic of the
   goal ([Ec<Logic>Transform]; for equiv, on the given side). The visible
   goals are those of that rule: the obligations of the transformation
   (only [kill] has one: [phoare [ks : true ==> true] = 1] for the killed
   statement [ks]), then the transformed judgement. As the derived tactics
   only differ by the transformation they apply, they share the
   logic-agnostic dispatcher [t_transform] below, and no per-logic module.

   [weakmem] is not a program transformation (it changes the memory type
   of a hypothesis and adds an implication): it has its own rule in each
   logic ([Ec<Logic>WeakMem], see [process_weakmem] below). *)

(* -------------------------------------------------------------------- *)
(* The memory and statement transformed: the program of the goal (hoare,
   ehoare, bdhoare) or of the given side (equiv). *)
let tx_stmt (side : oside) (tc : tcenv1) =
  match side, (FApi.tc1_goal tc).f_node with
  | None, FhoareS   hs -> (hs.hs_m, hs.hs_s)
  | None, FeHoareS  hs -> (hs.ehs_m, hs.ehs_s)
  | None, FbdHoareS hs -> (hs.bhs_m, hs.bhs_s)
  | None, _ ->
      tc_error_noXhl ~kinds:[`PHoare `Stmt; `Hoare `Stmt; `EHoare `Stmt] !!tc
  | Some side, _ ->
      let es = tc1_as_equivS tc in
      sideif side (es.es_ml, es.es_sl) (es.es_mr, es.es_sr)

(* Apply the transformation [tr] through the transformation rule of the
   logic of the goal (on the given side for equiv). *)
let t_transform (side : oside) (tr : EcPlTransform.transform) (tc : tcenv1) =
  match side, (FApi.tc1_goal tc).f_node with
  | None, FhoareS _ ->
      EcHoareTransform.t_hoare_transform { htr_tr = tr } tc
  | None, FeHoareS _ ->
      EcEHoareTransform.t_ehoare_transform { ehtr_tr = tr } tc
  | None, FbdHoareS _ ->
      EcBdHoareTransform.t_bdhoare_transform { btr_tr = tr } tc
  | None, _ ->
      tc_error_noXhl ~kinds:[`PHoare `Stmt; `Hoare `Stmt; `EHoare `Stmt] !!tc
  | Some side, _ ->
      EcEquivTransform.t_equiv_transform { etr_side = side; etr_tr = tr } tc

(* Resolve a code position of [s] (failing with "invalid code position"). *)
let resolve_cpos (tc : tcenv1) (cpos : Position.codepos) (s : stmt) =
  try  fst (snd (Zpr.zipper_of_cpos_r (FApi.tc1_env tc) cpos s))
  with Position.InvalidCPos -> tc_error !!tc "invalid code position"

(* -------------------------------------------------------------------- *)
let t_kill (side : oside) (cpos : Position.codepos) (olen : int option) tc =
  let _, s = tx_stmt side tc in
  let at = resolve_cpos tc cpos s in
  t_transform side (EcTrKill.TrKill { trk_at = at; trk_len = olen }) tc

(* -------------------------------------------------------------------- *)
let t_alias (side : oside) (cpos : Position.codepos) (id : psymbol option) tc =
  let _, s = tx_stmt side tc in
  let at = resolve_cpos tc cpos s in
  let name = odfl "x" (omap EcLocation.unloc id) in
  t_transform side (EcTrAlias.TrAlias { tral_at = at; tral_name = name }) tc

(* -------------------------------------------------------------------- *)
(* The [fresh] flag has no effect: the variable is always fresh. *)
let t_set (side : oside) (cpos : Position.codepos) ((_fresh, id) : bool * psymbol) e tc =
  let _, s = tx_stmt side tc in
  let at = resolve_cpos tc cpos s in
  t_transform side
    (EcTrSet.TrSet { trs_at = at; trs_name = EcLocation.unloc id; trs_e = e })
    tc

(* -------------------------------------------------------------------- *)
(* Find the subterm matched by the pattern in the expression of the
   instruction at the position, and its occurrences. *)
let t_set_match (side : oside) (cpos : Position.codepos) (id : EcSymbols.symbol) ((ue, mev, ptn) : _ * _ * form) tc =
  let pe = !!tc in
  let hyps = FApi.tc1_hyps tc in
  let me, s = tx_stmt side tc in
  let at = resolve_cpos tc cpos s in
  let zpr = Zpr.zipper_of_nm_cpos at s in

  let i, _ = List.destruct zpr.Zpr.z_tail in
  let e =
    let e, kind, _ =
      get_expression_of_instruction i |> ofdfl (fun () ->
        tc_error pe "targetted instruction should contain an expression"
      ) in

    match kind with
    | `Sasgn | `Srnd | `Sif | `Smatch -> e
    | `Swhile -> tc_error pe "while loops not supported"
  in

  let subf, occ =
    try
      let ptev = EcProofTerm.ptenv pe hyps (ue, mev) in
      let e = ss_inv_of_expr (fst me) e in
      let subf, occmode = EcProofTerm.pf_find_occurence_lazy ptev ~ptn e.inv in
      let subf = { m = e.m; inv = subf } in

      assert (EcProofTerm.can_concretize ptev);

      let occ =
        EcMatching.FPosition.select_form
          ~xconv:`AlphaEq ~keyed:occmode.k_keyed
          hyps None subf.inv e.inv in

      (subf, occ)

    with EcProofTerm.FindOccFailure _ ->
      tc_error pe "cannot find an occurrence of the pattern"
  in

  t_transform side
    (EcTrSetMatch.TrSetMatch
       { trsm_at = at; trsm_name = id; trsm_sub = subf; trsm_occ = occ; })
    tc

(* -------------------------------------------------------------------- *)
let t_cfold
  ~(eager : bool)
   (side  : side option)
   (cpos  : Position.codepos)
   (olen  : int option)
   (tc    : tcenv1)
=
  let _, s = tx_stmt side tc in
  let at = resolve_cpos tc cpos s in
  t_transform side
    (EcTrCFold.TrCFold { trcf_at = at; trcf_len = olen; trcf_eager = eager; })
    tc

(* -------------------------------------------------------------------- *)
let process_cfold (info : pcfold) tc =
  let cpos = EcLowPhlGoal.tc1_process_codepos tc (info.side, info.start) in
  t_cfold ~eager:info.eager info.side cpos info.length tc

let process_kill (side, cpos, len) tc =
  let cpos = EcLowPhlGoal.tc1_process_codepos tc (side, cpos) in
  t_kill side cpos len tc

let process_alias (side, cpos, id) tc =
  let cpos = EcLowPhlGoal.tc1_process_codepos tc (side, cpos) in
  t_alias side cpos id tc

let process_set (side, cpos, fresh, id, e) tc =
  let e = TTC.tc1_process_Xhl_exp tc side None e in
  let cpos = EcLowPhlGoal.tc1_process_codepos tc (side, cpos) in
  t_set side cpos (fresh, id) e tc

let process_set_match (side, cpos, id, pattern) tc =
  let cpos = EcLowPhlGoal.tc1_process_codepos tc (side, cpos) in
  let me, _ = tc1_get_stmt side tc in
  let hyps = LDecl.push_active_ss me (FApi.tc1_hyps tc) in
  let ue  = EcProofTyping.unienv_of_hyps hyps in
  let ptnmap = ref Mid.empty in
  let pattern = EcTyping.trans_pattern (LDecl.toenv hyps) ptnmap ue pattern in
  t_set_match side cpos (EcLocation.unloc id)
    (ue, EcMatching.MEV.of_idents (Mid.keys !ptnmap) `Form, pattern)
    tc

(* -------------------------------------------------------------------- *)
(* [weakmem h (xs : t)]: the hypothesis [h], a judgement on a statement,
   weakened by the fresh local variables [xs] (in the memory of the given
   side for equiv, both memories by default), is added as a premise of the
   goal. Derived in each logic (cut, then the [weakmem] rule of the logic
   of [h], [Ec<Logic>WeakMem]); the variables are typed first, the logic
   being then the one of [h]. *)
let process_weakmem (side, id, params) tc =
  let open EcLocation in
  let hyps = FApi.tc1_hyps tc in
  let env = FApi.tc1_env tc in
  let h, f =
    try LDecl.hyp_by_name (unloc id) hyps
    with LDecl.LdeclError _ ->
      tc_lookup_error !!tc ~loc:id.pl_loc `Local ([], unloc id)
  in

  let process_decl (x, ty) =
    let ty = EcTyping.transty EcTyping.tp_tydecl env (EcUnify.UniEnv.create None) ty in
    let x = omap unloc (unloc x) in
    { ov_name = x; ov_type = ty }
  in

  let decls = List.map process_decl params in

  let t =
    match f.f_node with
    | FhoareS _ ->
      EcHoareWeakMem.t_hoare_weakmem_hyp h { hwm_vars = decls }

    | FeHoareS _ ->
      EcEHoareWeakMem.t_ehoare_weakmem_hyp h { ehwm_vars = decls }

    | FbdHoareS _ ->
      EcBdHoareWeakMem.t_bdhoare_weakmem_hyp h { bwm_vars = decls }

    | FequivS _ ->
      EcEquivWeakMem.t_equiv_weakmem_hyp h side decls

    | _ ->
      tc_error ~loc:id.pl_loc !!tc
        "the hypothesis need to be a hoare/phoare/ehoare/equiv on statement"
  in

  try t tc
  with EcMemory.DuplicatedMemoryBinding x ->
    tc_error ~loc:id.pl_loc !!tc "variable %s already declared" x

(* -------------------------------------------------------------------- *)
(* [case <- p]: split the tuple assignment at [p]. The checks done before
   the transformation (and their failures, assertion failures and an
   uncaught [InvalidCPos] included) are those of the tactic before its
   migration. *)
let process_case ((side, pos) : side option * pcodepos) (tc : tcenv1) =
  let (env, _, concl) = FApi.tc1_eflat tc in

  let kinds = [`Hoare `Stmt; `EHoare `Stmt; `PHoare `Stmt; `Equiv `Stmt] in

  if not (EcLowPhlGoal.is_program_logic concl kinds) then
    assert false;

  let _, s = EcLowPhlGoal.tc1_get_stmt side tc in
  let pos = EcLowPhlGoal.tc1_process_codepos tc (side, pos) in
  let zpr, (at, _) = Zpr.zipper_of_cpos_r env pos s in

  let i =
    match zpr.Zpr.z_tail with
    | i :: _ -> i
    | [] -> raise Position.InvalidCPos in

  if not (is_asgn i) then
    tc_error !!tc "the code position should target an assignment";

  let lv, e = destr_asgn i in

  let pvl =
    match lv with
    | LvVar _ -> PV.empty
    | LvTuple lvs ->
      let lvs = List.tl (List.rev lvs) in
      let lvs = Option.get (lv_of_list lvs) in
      EcPV.lp_write env lvs in

  if not (EcPV.PV.indep env pvl (EcPV.e_read env e)) then
    assert false;

  t_transform side (EcTrAsgnCase.TrAsgnCase { trac_at = at }) tc

(* -------------------------------------------------------------------- *)
let t_transform_if (side : oside) (cpos : Position.codepos) (tc : tcenv1) =
  let _, s = tx_stmt side tc in
  let at = resolve_cpos tc cpos s in
  t_transform side (EcTrSimplifyIf.TrSimplifyIf { trsi_at = at }) tc

(* -------------------------------------------------------------------- *)
let t_transform_if_rec1 side g =
  let (_, s) = tc1_get_stmt side g in
  let test i =
    match i.i_node with
    | Sif (_, s1, s2) ->
        List.for_all is_asgn s1.s_node && List.for_all is_asgn s2.s_node
    | _ -> false
  in
  match Position.find_first_matching_instr test s with
  | Some cpos -> t_transform_if side cpos g
  | None -> tc_error (!!g) "no more transformation"

let t_transform_if_rec side g =
  FApi.t_repeat (t_transform_if_rec1 side) g

(* -------------------------------------------------------------------- *)
let process_transform_if (side, cpos) tc =
  match cpos with
  | None ->
      t_transform_if_rec side tc
  | Some cpos ->
      let cpos = EcLowPhlGoal.tc1_process_codepos tc (side, cpos) in
      t_transform_if side cpos tc
