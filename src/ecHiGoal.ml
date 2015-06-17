(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcLocation
open EcSymbols
open EcParsetree
open EcTypes
open EcFol
open EcEnv
open EcMatching

open EcBaseLogic

open EcProofTerm
open EcCoreGoal
open EcCoreGoal.FApi
open EcLowGoal

module Sid  = EcIdent.Sid
module Mid  = EcIdent.Mid
module Sp   = EcPath.Sp

module ER  = EcReduction
module PT  = EcProofTerm
module TT  = EcTyping
module TTC = EcProofTyping
module LG  = EcCoreLib.CI_Logic

(* -------------------------------------------------------------------- *)
type ttenv = {
  tt_provers    : EcParsetree.pprover_infos -> EcProvers.prover_infos;
  tt_smtmode    : [`Admit | `Strict | `Standard | `Report];
  tt_implicits  : bool;
}

type engine = ptactic_core -> FApi.backward

(* -------------------------------------------------------------------- *)
type focus_t = EcParsetree.tfocus

let process_tfocus tc (focus : focus_t) : tfocus =
  let count = FApi.tc_count tc in

  let check1 i =
    let error () = tc_error !$tc "invalid focus index: %d" i in
    if   i >= 0
    then if not (0 < i && i <= count) then error () else i-1
    else if -i > count then error () else count+i
  in

  let checkfs fs =
    List.fold_left
      (fun rg (i1, i2) ->
        let i1 = odfl min_int (omap check1 i1) in
        let i2 = odfl max_int (omap check1 i2) in
        if i1 <= i2 then ISet.add_range i1 i2 rg else rg)
      ISet.empty fs
  in

  let posfs = omap checkfs (fst focus) in
  let negfs = omap checkfs (snd focus) in

  fun i ->
       odfl true (posfs |> omap (ISet.mem i))
    && odfl true (negfs |> omap (fun fc -> not (ISet.mem i fc)))

(* -------------------------------------------------------------------- *)
let process_assumption (tc : tcenv1) =
  EcLowGoal.t_assumption `Conv tc

(* -------------------------------------------------------------------- *)
let process_reflexivity (tc : tcenv1) =
  try  EcLowGoal.t_reflex tc
  with InvalidGoalShape ->
    tc_error !!tc "cannot prove goal by reflexivity"

(* -------------------------------------------------------------------- *)
let process_trivial (tc : tcenv1) =
  EcPhlAuto.t_trivial tc

(* -------------------------------------------------------------------- *)
let process_done tc =
  let tc = process_trivial tc in

  if not (FApi.tc_done tc) then
    tc_error (FApi.tc_penv tc) "[by]: cannot close goals";
  tc

(* -------------------------------------------------------------------- *)
let process_change fp (tc : tcenv1) =
  let fp = TTC.tc1_process_formula tc fp in
  FApi.tcenv_of_tcenv1 (t_change fp tc)

(* -------------------------------------------------------------------- *)
let process_simplify ri (tc : tcenv1) =
  let env, hyps, _ = FApi.tc1_eflat tc in

  let do1 (sop, sid) ps =
    match ps.pl_desc with
    | ([], s) when LDecl.has_symbol s hyps ->
        let id = fst (LDecl.lookup s hyps) in
        (sop, Sid.add id sid)

    | qs ->
        match EcEnv.Op.lookup_opt qs env with
        | None   -> tc_lookup_error !!tc ~loc:ps.pl_loc `Operator qs
        | Some p -> (Sp.add (fst p) sop, sid)
  in

  let delta_p, delta_h =
    ri.pdelta
      |> omap (List.fold_left do1 (Sp.empty, Sid.empty))
      |> omap (fun (x, y) -> (Sp.mem^~ x, Sid.mem^~ y))
      |> odfl (predT, predT)
  in

  let ri = {
    EcReduction.beta    = ri.pbeta;
    EcReduction.delta_p = delta_p;
    EcReduction.delta_h = delta_h;
    EcReduction.zeta    = ri.pzeta;
    EcReduction.iota    = ri.piota;
    EcReduction.logic   = ri.plogic;
    EcReduction.modpath = ri.pmodpath;
  } in

    t_simplify_with_info ri tc

(* -------------------------------------------------------------------- *)

let process_smt ?loc (ttenv : ttenv) pi (tc : tcenv1) =
  let pi  = ttenv.tt_provers pi in

  match ttenv.tt_smtmode with
  | `Admit ->
      t_admit tc

  | (`Standard | `Strict) as mode ->
      t_seq (t_simplify ~delta:false) (t_smt ~mode pi) tc

  | `Report ->
      t_seq (t_simplify ~delta:false) (t_smt ~mode:(`Report loc) pi) tc

(* -------------------------------------------------------------------- *)
let process_clear symbols tc =
  let hyps = FApi.tc1_hyps tc in

  let toid s =
    if not (LDecl.has_symbol (unloc s) hyps) then
      tc_lookup_error !!tc ~loc:s.pl_loc `Local ([], unloc s);
    fst (LDecl.lookup (unloc s) hyps)
  in

  try  t_clears (List.map toid symbols) tc
  with ClearError err -> tc_error_clear !!tc err

(* -------------------------------------------------------------------- *)
module LowRewrite = struct
  type error =
  | LRW_NotAnEquation
  | LRW_NothingToRewrite
  | LRW_InvalidOccurence
  | LRW_CannotInfer

  exception RewriteError of error

  let rec find_rewrite_pattern (dir : rwside) hyps pt =
    let env = LDecl.toenv hyps in
    let ax  = pt.PT.ptev_ax in

    match EcFol.sform_of_form ax with
    | EcFol.SFeq  (f1, f2) -> (pt, (f1, f2))
    | EcFol.SFiff (f1, f2) -> (pt, (f1, f2))

    | EcFol.SFnot f ->
        let pt' = pt_of_global_r pt.ptev_env LG.p_negeqF [] in
        let pt' = apply_pterm_to_arg_r pt' (PVAFormula f) in
        let pt' = apply_pterm_to_arg_r pt' (PVASub pt) in
        (pt', (f, f_false))

    | _ -> begin
      match TTC.destruct_product hyps ax with
      | None ->
          if   dir = `LtoR && ER.EqTest.for_type env ax.f_ty tbool
          then (pt, (ax, f_true))
          else raise (RewriteError LRW_NotAnEquation)
      | Some _ ->
          let pt = EcProofTerm.apply_pterm_to_hole pt in
          find_rewrite_pattern dir hyps pt
    end

  let t_rewrite_r (s, o) pt tc =
    let hyps, concl = FApi.tc1_flat tc in

    let (pt, (f1, f2)) = find_rewrite_pattern s hyps pt in

    let fp = match s with `LtoR -> f1 | `RtoL -> f2 in

    (try  PT.pf_find_occurence ~keyed:true pt.PT.ptev_env ~ptn:fp concl
     with EcMatching.MatchFailure -> raise (RewriteError LRW_NothingToRewrite));

    if not (PT.can_concretize pt.PT.ptev_env) then
      raise (RewriteError LRW_CannotInfer);

    let fp   = PT.concretize_form pt.PT.ptev_env fp in
    let pt   = fst (PT.concretize pt) in
    let cpos =
      try  FPosition.select_form hyps o fp concl
      with InvalidOccurence -> raise (RewriteError (LRW_InvalidOccurence))
    in

    EcLowGoal.t_rewrite pt (s, Some cpos) tc

  let t_rewrite (s, o) pt (tc : tcenv1) =
    let hyps   = FApi.tc1_hyps tc in
    let pt, ax = LowApply.check `Elim pt (`Hyps (hyps, !!tc)) in
    let ptenv  = ptenv_of_penv hyps !!tc in

    t_rewrite_r (s, o) { ptev_env = ptenv; ptev_pt = pt; ptev_ax = ax; } tc

  let t_autorewrite lemmas (tc : tcenv1) =
    let pts =
      let do1 lemma =
        PT.pt_of_uglobal !!tc (FApi.tc1_hyps tc) lemma in
      List.map do1 lemmas
    in

    let try1 pt tc =
      let pt = { pt with PT.ptev_env = PT.copy pt.ptev_env } in
        try  t_rewrite_r (`LtoR, None) pt tc
        with RewriteError _ -> raise InvalidGoalShape
    in

      t_do_r ~focus:0 `Maybe None (t_ors (List.map try1 pts)) !@tc
end

let t_rewrite_prept info pt tc = 
  LowRewrite.t_rewrite_r info (pt_of_prept tc pt) tc

(* -------------------------------------------------------------------- *)
let process_rewrite1_core (s, o) pt tc =
  try
    LowRewrite.t_rewrite_r (s, o) pt tc
  with
  | LowRewrite.RewriteError e ->
      match e with
      | LowRewrite.LRW_NotAnEquation ->
          tc_error !!tc "not an equation to rewrite"
      | LowRewrite.LRW_NothingToRewrite ->
          tc_error !!tc "nothing to rewrite"
      | LowRewrite.LRW_InvalidOccurence ->
          tc_error !!tc "invalid occurence selector"
      | LowRewrite.LRW_CannotInfer ->
          tc_error !!tc "cannot infer all placeholders"

(* -------------------------------------------------------------------- *)
let process_delta (s, o, p) tc =
  let env, hyps, concl = FApi.tc1_eflat tc in

  match unloc p with
  | PFident ({ pl_desc = ([], x) }, None)
      when s = `LtoR && EcUtils.is_none o ->

    let check_op = fun p -> sym_equal (EcPath.basename p) x in
    let check_id = fun y -> sym_equal (EcIdent.name y) x in
    let concl = EcReduction.simplify
      { EcReduction.no_red with
          EcReduction.delta_p = check_op;
          EcReduction.delta_h = check_id; }
      hyps concl

    in FApi.tcenv_of_tcenv1 (t_change concl tc)

  | _ ->

  (* Continue with matching based unfolding *)
  let (ptenv, p) =
    let (ps, ue), p = TTC.tc1_process_pattern tc p in
    let ev = MEV.of_idents (Mid.keys ps) `Form in
      (ptenv !!tc hyps (ue, ev), p)
  in

  let (tvi, tparams, body, args) =
    match sform_of_form p with
    | SFop (p, args) -> begin
        let op = EcEnv.Op.by_path (fst p) env in

        match op.EcDecl.op_kind with
        | EcDecl.OB_oper (Some (EcDecl.OP_Plain e)) ->
            (snd p, op.EcDecl.op_tparams, form_of_expr EcFol.mhr e, args)
        | EcDecl.OB_pred (Some f) ->
            (snd p, op.EcDecl.op_tparams, f, args)
        | _ ->
            tc_error !!tc "the operator is not transparent"
    end

  | SFlocal x when LDecl.reducible_var x hyps ->
      ([], [], LDecl.reduce_var x hyps, [])

  | _ -> tc_error !!tc "not headed by an operator/predicate"

  in

  let na = List.length args in

  match s with
  | `LtoR -> begin
    let matches =
      try  PT.pf_find_occurence ptenv ~ptn:p concl; true
      with EcMatching.MatchFailure -> false
    in

    if matches then begin
      let p    = concretize_form ptenv p in
      let cpos =
        let test = fun _ fp ->
          let fp =
            match fp.f_node with
            | Fapp (h, hargs) when List.length hargs > na ->
                let (a1, a2) = List.takedrop na hargs in
                  f_app h a1 (toarrow (List.map f_ty a2) fp.f_ty)
            | _ -> fp
          in
            if   EcReduction.is_alpha_eq hyps p fp
            then `Accept (-1)
            else `Continue
        in
          try  FPosition.select ?o test concl
          with InvalidOccurence ->
            tc_error !!tc "invalid occurences selector"
      in

      let concl =
        FPosition.map cpos
          (fun topfp ->
            let (fp, args) = EcFol.destr_app topfp in

            match sform_of_form fp with
            | SFop ((_, tvi), []) -> begin
              (* FIXME: TC HOOK *)
              let subst = EcTypes.Tvar.init (List.map fst tparams) tvi in
              let body  = EcFol.Fsubst.subst_tvar subst body in
              let body  = f_app body args topfp.f_ty in
                try  EcReduction.h_red EcReduction.beta_red hyps body
                with EcBaseLogic.NotReducible -> body
            end

            | SFlocal _ -> begin
                assert (tparams = []);
                let body = f_app body args topfp.f_ty in
                  try  EcReduction.h_red EcReduction.beta_red hyps body
                  with EcBaseLogic.NotReducible -> body
            end

            | _ -> assert false)
          concl
      in
        FApi.tcenv_of_tcenv1 (t_change concl tc)
    end else t_id tc
  end

  | `RtoL ->
    let fp =
      (* FIXME: TC HOOK *)
      let subst = EcTypes.Tvar.init (List.map fst tparams) tvi in
      let body  = EcFol.Fsubst.subst_tvar subst body in
      let fp    = f_app body args p.f_ty in
        try  EcReduction.h_red EcReduction.beta_red hyps fp
        with EcBaseLogic.NotReducible -> fp
    in

    let matches =
      try  PT.pf_find_occurence ptenv ~ptn:fp concl; true
      with EcMatching.MatchFailure -> false
    in

    if matches then begin
      let p    = concretize_form ptenv p  in
      let fp   = concretize_form ptenv fp in
      let cpos =
        try  FPosition.select_form hyps o fp concl
        with InvalidOccurence ->
          tc_error !!tc "invalid occurences selector"
      in

      let concl = FPosition.map cpos (fun _ -> p)  concl in
        FApi.tcenv_of_tcenv1 (t_change concl tc)
    end else t_id tc

(* -------------------------------------------------------------------- *)
let rec process_rewrite1 ttenv ri tc =
  let implicits = function
  | `Implicit -> ttenv.tt_implicits
  | `Explicit -> false in

  match unloc ri with
  | RWDone b ->
      let tt = if b then t_simplify ~delta:false else t_id in
      FApi.t_seq tt process_trivial tc

  | RWSimpl ->
      t_simplify ~delta:false tc

  | RWDelta ((s, r, o), p) -> begin
      let do1 tc = process_delta (s, o, p) tc in

      match r with
      | None -> do1 tc
      | Some (b, n) -> t_do b n do1 tc
  end

  | RWRw (((s : rwside), r, o), pts) -> begin
      let do1 ((subs : rwside), (mode, pt)) tc =
        let theside =
          match s, subs with
          | `LtoR, _     -> (subs  :> rwside)
          | _    , `LtoR -> (s     :> rwside)
          | `RtoL, `RtoL -> (`LtoR :> rwside) in

        let is_baserw p tc = 
          EcEnv.BaseRw.is_base p.pl_desc (FApi.tc1_env tc) in

        match pt with 
        | { fp_head = FPNamed (p, None); fp_args = []; }
              when mode = `Implicit && is_baserw p tc
        ->
          let env = FApi.tc1_env tc in
          let ls  = snd (EcEnv.BaseRw.lookup p.pl_desc env) in
          let ls  = EcPath.Sp.elements ls in

          let do1 lemma tc =
            let pt = PT.pt_of_uglobal !!tc (FApi.tc1_hyps tc) lemma in
              process_rewrite1_core (theside, o) pt tc in
            t_ors (List.map do1 ls) tc

        | { fp_head = FPNamed (p, None); fp_args = []; }
              when mode = `Implicit
        ->
          let env = FApi.tc1_env tc in
          let pt  = PT.tc1_process_full_pterm ~implicits:(implicits mode) tc pt in

          if    is_ptglobal pt.PT.ptev_pt.pt_head
             && List.is_empty pt.PT.ptev_pt.pt_args
          then begin
            let ls = EcEnv.Ax.all ~name:(unloc p) env in

            let do1 (lemma, _) tc =
              let pt = PT.pt_of_uglobal !!tc (FApi.tc1_hyps tc) lemma in
                process_rewrite1_core (theside, o) pt tc in
              t_ors (List.map do1 ls) tc
          end else
            process_rewrite1_core (theside, o) pt tc

        | _ ->
          let pt = PT.tc1_process_full_pterm ~implicits:(implicits mode) tc pt in
          process_rewrite1_core (theside, o) pt tc
        in

      let doall tc = t_ors (List.map do1 pts) tc in

      match r with
      | None -> doall tc
      | Some (b, n) -> t_do b n doall tc
  end

  | RWPr (x,f) -> EcPhlPrRw.t_pr_rewrite (unloc x, f) tc

  | RWSmt info ->
      process_smt ~loc:ri.pl_loc ttenv info tc

(* -------------------------------------------------------------------- *)
let process_rewrite ttenv ri tc =
  let do1 tc (fc, ri) =
    let tx =
      match fc |> omap ((process_tfocus tc) |- unloc) with
      | None    -> FApi.t_onall
      | Some fc -> (fun tc -> FApi.t_onselect fc tc)
    in
      tx (process_rewrite1 ttenv ri) tc
  in
  List.fold_left do1 (tcenv_of_tcenv1 tc) ri

(* -------------------------------------------------------------------- *)
let process_view1 pe tc =
  let module E = struct
    exception NoInstance
    exception NoTopAssumption
  end in

  let destruct hyps fp =
    let doit fp =
      match EcFol.sform_of_form fp with
      | SFquant (Lforall, (x, t), lazy f) -> `Forall (x, t, f)
      | SFimp (f1, f2) -> `Imp (f1, f2)
      | SFiff (f1, f2) -> `Iff (f1, f2)
      | _ -> raise EcProofTyping.NoMatch
    in
      EcProofTyping.lazy_destruct hyps doit fp
  in

  let rec instantiate fp ids pte =
    let hyps = pte.PT.ptev_env.PT.pte_hy in

    match destruct hyps pte.PT.ptev_ax with
    | None -> raise E.NoInstance

    | Some (`Forall (x, xty, _)) ->
        instantiate fp ((x, xty) :: ids) (PT.apply_pterm_to_hole pte)

    | Some (`Imp (f1, f2)) -> begin
        try
          PT.pf_form_match ~mode:fmdelta pte.PT.ptev_env ~ptn:f1 fp;
          (pte, ids, f2, `None)
        with MatchFailure -> raise E.NoInstance
    end

    | Some (`Iff (f1, f2)) -> begin
        try
          PT.pf_form_match ~mode:fmdelta pte.PT.ptev_env ~ptn:f1 fp;
          (pte, ids, f2, `IffLR (f1, f2))
        with MatchFailure -> raise E.NoInstance
    end
  in

  try
    match TTC.destruct_product (tc1_hyps tc) (FApi.tc1_goal tc) with
    | None | Some (`Forall _) -> raise E.NoTopAssumption

    | Some (`Imp (_, _)) when pe.fp_head = FPCut None ->
        let hyps = FApi.tc1_hyps tc in
        let hid  = LDecl.fresh_id hyps "h" in
        let hqs  = mk_loc _dummy ([], EcIdent.name hid) in
        let pe   = { pe with fp_head = FPNamed (hqs, None) } in

        t_intros_i_seq ~clear:true [hid]
          (fun tc ->
            let pe = PT.tc1_process_full_pterm tc pe in

            if not (PT.can_concretize pe.PT.ptev_env) then
              tc_error !!tc "cannot infer all placeholders";
              let pt, ax = PT.concretize pe in t_cutdef pt ax tc)
          tc

    | Some (`Imp (f1, _)) ->
        let top    = LDecl.fresh_id (tc1_hyps tc) "h" in
        let tc     = t_intros_i_1 [top] tc in
        let hyps   = tc1_hyps tc in
        let pte    = PT.tc1_process_full_pterm tc pe in
        let inargs = List.length pte.PT.ptev_pt.pt_args in

        let (pte, ids, cutf, view) = instantiate f1 [] pte in

        let evm  = !(pte.PT.ptev_env.PT.pte_ev) in
        let args = List.drop inargs pte.PT.ptev_pt.pt_args in
        let args = List.combine (List.rev ids) args in

        let ids =
          let for1 ((_, ty) as idty, arg) =
            match ty, arg with
            | GTty _, PAFormula { f_node = Flocal x } when MEV.mem x `Form evm ->
                if MEV.isset x `Form evm then None else Some (x, idty)

            | GTmem _, PAMemory x when MEV.mem x `Mem evm ->
                if MEV.isset x `Mem evm then None else Some (x, idty)

            | _, _ -> assert false

          in List.pmap for1 args
        in

        let cutf =
          let ptenv = PT.copy pte.PT.ptev_env in

          let for1 evm (x, idty) =
            match idty with
            | id, GTty    ty -> evm := MEV.set x (`Form (f_local id ty)) !evm
            | id, GTmem   _  -> evm := MEV.set x (`Mem id) !evm
            | _ , GTmodty _  -> assert false
          in

          List.iter (for1 ptenv.PT.pte_ev) ids;

          if not (PT.can_concretize ptenv) then
            tc_error !!tc "cannot infer all type variables";

          PT.concretize_e_form
            (PT.concretize_env ptenv)
            (f_forall (List.map snd ids) cutf)
        in

        let discharge tc =
          let intros = List.map (EcIdent.name |- fst |- snd) ids in
          let intros = LDecl.fresh_ids hyps intros in

          let for1 evm (x, idty) id =
            match idty with
            | _, GTty   ty -> evm := MEV.set x (`Form (f_local id ty)) !evm
            | _, GTmem   _ -> evm := MEV.set x (`Mem id) !evm
            | _, GTmodty _ -> assert false

          in

          let tc = EcLowGoal.t_intros_i_1 intros tc in

          List.iter2 (for1 pte.PT.ptev_env.PT.pte_ev) ids intros;

          let pte =
            match view with
            | `None -> pte
            | `IffLR (f1, f2) ->
                let vpte = PT.pt_of_global_r pte.PT.ptev_env LG.p_iff_lr [] in
                let vpte = PT.apply_pterm_to_arg_r vpte (PVAFormula f1) in
                let vpte = PT.apply_pterm_to_arg_r vpte (PVAFormula f2) in
                let vpte = PT.apply_pterm_to_arg_r vpte (PVASub pte) in
                vpte
          in

          let pt = fst (PT.concretize (PT.apply_pterm_to_hole pte)) in

          FApi.t_seq
            (EcLowGoal.t_apply pt)
            (EcLowGoal.t_apply_hyp top)
            tc
        in

        FApi.t_internal
          (FApi.t_seqsub (EcLowGoal.t_cut cutf)
             [EcLowGoal.t_close ~who:"view" discharge;
              EcLowGoal.t_clear top])
          tc

  with
  | E.NoInstance ->
      tc_error !!tc "cannot apply view"
  | E.NoTopAssumption ->
      tc_error !!tc "no top assumption"

(* -------------------------------------------------------------------- *)
let process_view pes tc =
  let views = List.map (t_last |- process_view1) pes in
  List.fold_left (fun tc tt -> tt tc) (FApi.tcenv_of_tcenv1 tc) views

(* -------------------------------------------------------------------- *)
let process_mintros ?(cf = true) pis gs =
  let mk_intro ids tc =
    t_intros (snd (List.map_fold (fun (hyps, form) s ->
      let rec destruct fp =
        match EcFol.sform_of_form fp with
        | SFquant (Lforall, (x, _)  , lazy fp) -> (EcIdent.name x, fp)
        | SFlet   (LSymbol (x, _), _, fp)      -> (EcIdent.name x, fp)
        | SFimp   (_                , fp)      -> ("H", fp)
        | _ -> begin
          match EcReduction.h_red_opt EcReduction.full_red hyps fp with
          | None   -> ("_", f_true)
          | Some f -> destruct f
        end
      in
      let name, form = destruct form in
      let id =
        lmap (function
        | `NoName       -> EcIdent.create "_"
        | `FindName     -> LDecl.fresh_id hyps name
        | `NoRename s   -> EcIdent.create s
        | `WithRename s -> LDecl.fresh_id hyps s) s
      in

      let hyps = LDecl.add_local id.pl_desc (LD_var (tbool, None)) hyps in
        (hyps, form), Tagged (unloc id, Some id.pl_loc))
      (FApi.tc1_flat tc) ids)) tc
  in

  let rec collect acc core pis =
    let maybe_core () =
      match core with
      | [] -> acc
      | _  -> `Core (List.rev core) :: acc
    in

    match pis with
    | [] -> maybe_core ()

    | IPCore x :: pis ->
        collect acc (x :: core) pis

    | IPDone b :: pis ->
        collect (`Done b :: maybe_core ()) [] pis

    | IPSimplify :: pis ->
        collect (`Simpl :: maybe_core ()) [] pis

    | IPClear xs :: pis ->
        collect (`Clear xs :: maybe_core ()) [] pis

    | IPCase (mode, x) :: pis ->
        let x = List.map (List.rev -| collect [] []) x in
          collect (`Case (mode, x) :: maybe_core ()) [] pis

    | IPRw x :: pis ->
        collect (`Rw x :: maybe_core ()) [] pis

    | IPView x :: pis ->
        collect (`View x :: maybe_core ()) [] pis

    | IPSubst x :: pis ->
        collect (`Subst x :: maybe_core ()) [] pis
  in

  let rec dointro nointro pis (gs : tcenv) =
    let (_, gs) =
      List.fold_left
        (fun (nointro, gs) ip ->
          match ip with
          | `Core ids ->
              (false, t_onall (mk_intro ids) gs)

          | `Done b   ->
              let t =
                let t_trivial = EcPhlAuto.t_trivial in
                match b with
                | true  -> t_seq (t_simplify ~delta:false) t_trivial
                | false -> t_trivial
              in
                (nointro, t_onall t gs)

          | `Simpl ->
              (nointro, t_onall (t_simplify ~delta:false) gs)

          | `Clear xs ->
              (nointro, t_onall (process_clear xs) gs)

          | `Case (mode, pis) ->
              let onsub gs =
                if FApi.tc_count gs <> List.length pis then
                  tc_error !$gs
                    "not the right number of intro-patterns (got %d, expecting %d)"
                    (List.length pis) (FApi.tc_count gs);
                t_sub (List.map (dointro1 false) pis) gs in

              let tc = t_or (t_elimT_ind `Case) t_elim in
              let tc = match mode with `One -> tc | `Full -> t_do `Maybe None tc in
              let tc =
                fun g ->
                  try  tc g
                  with InvalidGoalShape ->
                    tc_error !!g "invalid intro-pattern: nothing to eliminate"
              in     

              let gs =
                match nointro && not cf with
                | true when mode = `One -> onsub gs
                | _ -> begin
                    match pis with
                    | [] -> t_onall tc gs
                    | _  -> t_onall (fun gs -> onsub (tc gs)) gs
                end
              in
                (false, gs)

          | `Rw (o, s) ->
              let t tc =
                let h = EcIdent.create "_" in
                let rwt tc =
                  let pt = PT.pt_of_hyp !!tc (FApi.tc1_hyps tc) h in
                  process_rewrite1_core (s, o) pt tc
                in
                  t_seqs [t_intros_i [h]; rwt; t_clear h] tc
              in
                (false, t_onall t gs)

          | `View pe ->
              (false, t_onall (process_view1 pe) gs)

          | `Subst d ->
              let t tc =
                try
                  t_intros_i_seq ~clear:true [EcIdent.create "_"]
                    (EcLowGoal.t_subst ~clear:false ~tside:(d :> tside))
                    tc
                with InvalidGoalShape ->
                  tc_error !!tc "nothing to substitute"
              in
                (false, t_onall t gs))

        (nointro, gs) pis
    in
      gs

  and dointro1 nointro pis tc =
    dointro nointro pis (FApi.tcenv_of_tcenv1 tc) in

    dointro true (List.rev (collect [] [] pis)) gs

(* -------------------------------------------------------------------- *)
let process_intros ?cf pis tc =
  process_mintros ?cf pis (FApi.tcenv_of_tcenv1 tc)

(* -------------------------------------------------------------------- *)
let process_generalize1 pattern (tc : tcenv1) =
  let hyps, concl = FApi.tc1_flat tc in

  let onresolved pattern =
    match pattern with
    | `Form (occ, pf) -> begin
        match pf.pl_desc with
        | PFident ({pl_desc = ([], s)}, None)
            when occ = None && LDecl.has_symbol s hyps
          ->
            let id = fst (LDecl.lookup s hyps) in
            t_generalize_hyp ~clear:true id tc

        | _ ->
          let (ptenv, p) =
            let (ps, ue), p = TTC.tc1_process_pattern tc pf in
            let ev = MEV.of_idents (Mid.keys ps) `Form in
              (ptenv !!tc hyps (ue, ev), p)
          in

          (try  PT.pf_find_occurence ptenv ~ptn:p concl
           with EcMatching.MatchFailure -> tc_error !!tc "cannot find an occurence");

          let p    = PT.concretize_form ptenv p in
          let cpos =
            try  FPosition.select_form hyps occ p concl
            with InvalidOccurence -> tacuerror "invalid occurence selector"
          in

          let name =
            match EcParsetree.pf_ident pf with
            | None ->
                EcIdent.create "x"
            | Some x when EcIo.is_sym_ident x ->
                EcIdent.create x
            | Some _ ->
                EcIdent.create (EcTypes.symbol_of_ty p.f_ty)
          in

          let name, newconcl = FPosition.topattern ~x:name cpos concl in
          let newconcl = f_forall [(name, GTty p.f_ty)] newconcl in
          let pt = { pt_head = PTCut newconcl; pt_args = [PAFormula p]; } in

          EcLowGoal.t_apply pt tc

    end

    | `ProofTerm fp -> begin
        match fp.fp_head with
        | FPNamed ({ pl_desc = ([], s) }, None)
            when LDecl.has_symbol s hyps && List.is_empty fp.fp_args
          ->
            let id = fst (LDecl.lookup s hyps) in
            t_generalize_hyp ~clear:true id tc

        | _ ->
          let pt = PT.tc1_process_full_pterm tc fp in
          if not (PT.can_concretize pt.PT.ptev_env) then
            tc_error !!tc "cannot infer all placeholders";
          let pt, ax = PT.concretize pt in
          t_cutdef pt ax tc
    end
  in

  match ffpattern_of_genpattern hyps pattern with
  | Some ff -> onresolved (`ProofTerm ff)
  | None    -> onresolved pattern

(* -------------------------------------------------------------------- *)
let process_generalize patterns (tc : tcenv1) =
  try
    FApi.t_seqs (List.rev_map process_generalize1 patterns) tc
  with EcCoreGoal.ClearError err ->
    tc_error_clear !!tc err

(* -------------------------------------------------------------------- *)
let process_move views patterns (tc : tcenv1) =
  t_seq (process_generalize patterns) (process_view views) tc

(* -------------------------------------------------------------------- *)
let process_pose xsym o p (tc : tcenv1) =
  let (hyps, concl) = FApi.tc1_flat tc in

  let (ptenv, p) =
    let (ps, ue), p = TTC.tc1_process_pattern tc p in
    let ev = MEV.of_idents (Mid.keys ps) `Form in
      (ptenv !!tc hyps (ue, ev), p)
  in

  let dopat =
    try  PT.pf_find_occurence ptenv ~ptn:p concl; true
    with MatchFailure ->
      if not (PT.can_concretize ptenv) then
        if not (EcMatching.MEV.filled !(ptenv.PT.pte_ev)) then
          tc_error !!tc "cannot find an occurence"
        else
          tc_error !!tc "%s - %s"
            "cannot find an occurence"
            "instanciate type variables manually"
      else
        false
  in

  let p = PT.concretize_form ptenv p in

  let (x, letin) =
    match dopat with
    | false -> (EcIdent.create (unloc xsym), concl)
    | true  -> begin
        let cpos =
          try  FPosition.select_form hyps o p concl
          with InvalidOccurence -> tacuerror "invalid occurence selector"
        in
          FPosition.topattern ~x:(EcIdent.create (unloc xsym)) cpos concl
    end
  in

  let letin = EcFol.f_let1 x p letin in

  FApi.t_seq
    (fun tc -> tcenv_of_tcenv1 (t_change letin tc))
    (t_intros [Tagged (x, Some xsym.pl_loc)]) tc

(* -------------------------------------------------------------------- *)
module LowApply = struct
  exception NoInstance

  let t_apply_bwd_r pt (tc : tcenv1) =
    let (hyps, concl) = FApi.tc1_flat tc in

    let rec instantiate canview istop pt =
      match istop && PT.can_concretize pt.PT.ptev_env with
      | true ->
          let ax = PT.concretize_form pt.PT.ptev_env pt.PT.ptev_ax in
          if   EcReduction.is_conv hyps ax concl
          then pt
          else instantiate canview false pt

      | false -> begin
          try
            PT.pf_form_match ~mode:fmdelta pt.PT.ptev_env ~ptn:pt.PT.ptev_ax concl;
            if not (PT.can_concretize pt.PT.ptev_env) then
              raise NoInstance;
            pt
          with EcMatching.MatchFailure ->
            match TTC.destruct_product hyps pt.PT.ptev_ax with
            | Some _ ->
                (* FIXME: add internal marker *)
                instantiate canview false (PT.apply_pterm_to_hole pt)

            | None when not canview ->
                raise NoInstance

            | None ->
                let forview (p, fs) =
                  (* Current proof-term is view argument *)
                  (* Copy PT environment to set a back-track point *)
                  let argpt = { pt with ptev_env = PT.copy pt.ptev_env } in
                  let argpt = { ptea_env = argpt.ptev_env;
                                ptea_arg = PVASub argpt; } in

                  (* Type-check view - FIXME: the current API is perfectible *)
                  let viewpt =
                    { pt_head = PTGlobal (p, []);
                      pt_args = List.map (fun f -> PAFormula f) fs; } in
                  let viewpt, ax = LowApply.check `Elim viewpt (`Hyps (hyps, !!tc)) in

                  (* Apply view to its actual arguments *)
                  let viewpt = apply_pterm_to_arg
                      { ptev_env = argpt.ptea_env;
                        ptev_pt  = viewpt;
                        ptev_ax  = ax; }
                      argpt
                  in
                  try  Some (instantiate false true viewpt)
                  with NoInstance -> None
                in

                let views =
                  match sform_of_form pt.PT.ptev_ax with
                  | SFiff (f1, f2) ->
                      [(LG.p_iff_lr, [f1; f2]);
                       (LG.p_iff_rl, [f1; f2])]

                  | SFnot f1 ->
                      [(LG.p_negbTE, [f1])]

                  | _ -> []
                in

                try  List.find_map forview views
                with Not_found -> raise NoInstance
      end
    in

    let pt = instantiate true true pt in
    let pt = fst (PT.concretize pt) in

    EcLowGoal.t_apply pt tc

  let t_apply_bwd pt (tc : tcenv1) =
    let hyps   = FApi.tc1_hyps tc in
    let pt, ax = LowApply.check `Elim pt (`Hyps (hyps, !!tc)) in
    let ptenv  = ptenv_of_penv hyps !!tc in

    t_apply_bwd_r { ptev_env = ptenv; ptev_pt = pt; ptev_ax = ax; } tc
end

let t_apply_prept pt tc = 
  LowApply.t_apply_bwd_r (pt_of_prept tc pt) tc

(* -------------------------------------------------------------------- *)
let process_apply_bwd ~implicits mode (ff : ppterm) (tc : tcenv1) =
  try
    let pt   = PT.tc1_process_full_pterm ~implicits tc ff in
    let aout = LowApply.t_apply_bwd_r pt tc in

    match mode with
    | `Apply -> aout
    | `Exact ->
        let aout = FApi.t_onall process_trivial aout in
        if not (FApi.tc_done aout) then
          tc_error !!tc "cannot close goal";
        aout

  with LowApply.NoInstance ->
    tc_error !!tc "cannot apply lemma"

(* -------------------------------------------------------------------- *)
let process_apply_fwd ~implicits (pe, hyp) tc =
  let module E = struct exception NoInstance end in

  let hyps = FApi.tc1_hyps tc in

  if not (LDecl.has_hyp (unloc hyp) hyps) then
    tc_error !!tc "unknown hypothesis: %s" (unloc hyp);

  let hyp, fp = LDecl.lookup_hyp (unloc hyp) hyps in
  let pte = PT.tc1_process_full_pterm ~implicits tc pe in

  let rec instantiate pte =
    match TTC.destruct_product hyps pte.PT.ptev_ax with
    | None -> raise E.NoInstance

    | Some (`Forall _) ->
        instantiate (PT.apply_pterm_to_hole pte)

    | Some (`Imp (f1, f2)) ->
        try
          PT.pf_form_match ~mode:fmdelta pte.PT.ptev_env ~ptn:f1 fp;
          (pte, f2)
        with MatchFailure -> raise E.NoInstance
  in

  try
    let (pte, cutf) = instantiate pte in
    let pt = fst (PT.concretize pte) in
    let pt = { pt with pt_args = pt.pt_args @ [palocal hyp]; } in
    let cutf = PT.concretize_form pte.PT.ptev_env cutf in

    FApi.t_last
      (FApi.t_seq (t_clear hyp) (t_intros_i [hyp]))
      (t_cutdef pt cutf tc)

  with E.NoInstance ->
    tc_error !!tc "cannot apply lemma"

(* -------------------------------------------------------------------- *)
type apply_t = EcParsetree.apply_info

let process_apply ~implicits (infos : apply_t) tc =
  let implicits = function
    | `Implicit -> implicits
    | `Explicit -> false
  in

  match infos with
  | `ApplyIn ((mode, pe), tg) ->
      process_apply_fwd ~implicits:(implicits mode) (pe, tg) tc

  | `Apply (pe, mode) ->
      let for1 tc (mode, pe) =
        t_last (process_apply_bwd ~implicits:(implicits mode) `Apply pe) tc in
      let tc = List.fold_left for1 (tcenv_of_tcenv1 tc) pe in
      if mode = `Exact then t_onall process_done tc else tc

(* -------------------------------------------------------------------- *)
let process_subst syms (tc : tcenv1) =
  let resolve symp =
    let sym = TTC.tc1_process_form_opt tc None symp in

    match sym.f_node with
    | Flocal id        -> `Local id
    | Fglob  (mp, mem) -> `Glob  (mp, mem)
    | Fpvar  (pv, mem) -> `PVar  (pv, mem)

    | _ ->
      tc_error !!tc ~loc:symp.pl_loc
        "this formula is not subject to substitution"
  in

  match List.map resolve syms with
  | []   -> t_repeat t_subst tc
  | syms -> FApi.t_seqs (List.map (fun var tc -> t_subst ~var tc) syms) tc

(* -------------------------------------------------------------------- *)
type cut_t = intropattern * pformula * (ptactics located) option

let process_cut engine ((ip, phi, t) : cut_t) tc =
  let phi = TTC.tc1_process_formula tc phi in
  let tc  = EcLowGoal.t_cut phi tc in
  let tc  =
    match t with
    | None -> tc
    | Some t ->
       let t = mk_loc (loc t) (Pby (Some (unloc t))) in
       FApi.t_first (engine t) tc

  in FApi.t_last (process_intros ip) tc

(* -------------------------------------------------------------------- *)
type cutdef_t = intropattern * pcutdef

let process_cutdef (ip, pt) (tc : tcenv1) =
  let pt = { fp_head = FPNamed (pt.ptcd_name, pt.ptcd_tys);
             fp_args = pt.ptcd_args; } in
  let pt = PT.tc1_process_full_pterm tc pt in

  if not (PT.can_concretize pt.ptev_env) then
    tc_error !!tc "cannot infer all placeholders";

  let pt, ax = PT.concretize pt in

  FApi.t_sub
    [EcLowGoal.t_apply pt; process_intros ip]
    (t_cut ax tc)

(* -------------------------------------------------------------------- *)
let process_left (tc : tcenv1) =
  EcLowGoal.t_left tc

(* -------------------------------------------------------------------- *)
let process_right (tc : tcenv1) =
  EcLowGoal.t_right tc

(* -------------------------------------------------------------------- *)
let process_split (tc : tcenv1) =
  EcLowGoal.t_split tc

(* -------------------------------------------------------------------- *)
let process_elimT qs tc =
  let noelim () = tc_error !!tc "cannot recognize elimination principle" in

  let (hyps, concl) = FApi.tc1_flat tc in

  let (pf, pfty, _concl) =
    match sform_of_form concl with
    | SFquant (Lforall, (x, GTty xty), concl) -> (x, xty, concl)
    | _ -> noelim ()
  in

  let pf = LDecl.fresh_id hyps (EcIdent.name pf) in
  let tc = t_intros_i_1 [pf] tc in

  let (hyps, concl) = FApi.tc1_flat tc in

  let pt = PT.tc1_process_full_pterm tc qs in

  let (_xp, xpty, ax) =
    match TTC.destruct_product hyps pt.ptev_ax with
    | Some (`Forall (xp, GTty xpty, f)) -> (xp, xpty, f)
    | _ -> noelim ()
  in

  begin
    let ue = pt.ptev_env.pte_ue in
    try  EcUnify.unify (LDecl.toenv hyps) ue (tfun pfty tbool) xpty
    with EcUnify.UnificationFailure _ -> noelim ()
  end;

  if not (PT.can_concretize pt.ptev_env) then noelim ();

  let ax = PT.concretize_form pt.ptev_env ax in

  let rec skip ax =
    match TTC.destruct_product hyps ax with
    | Some (`Imp (_f1, f2)) -> skip f2
    | Some (`Forall (x, GTty xty, f)) -> ((x, xty), f)
    | _ -> noelim ()
  in

  let ((x, _xty), ax) = skip ax in

  let fpf  = f_local pf pfty in

  let ptnpos = FPosition.select_form hyps None fpf concl in
  let (_xabs, body) = FPosition.topattern ~x:x ptnpos concl in

  let rec skipmatch ax body sk =
    match TTC.destruct_product hyps ax, TTC.destruct_product hyps body with
    | Some (`Imp (i1, f1)), Some (`Imp (i2, f2)) ->
        if   EcReduction.is_alpha_eq hyps i1 i2
        then skipmatch f1 f2 (sk+1)
        else sk
    | _ -> sk
  in

  let sk = skipmatch ax body 0 in

  t_seqs
    [t_elimT_form (fst (PT.concretize pt)) ~sk fpf;
     t_or
       (t_clear pf)
       (t_seq (t_generalize_hyp pf) (t_clear pf));
     t_simplify_with_info EcReduction.beta_red]
    tc

(* -------------------------------------------------------------------- *)
let process_elim (pe, qs) tc =
  let doelim tc =
    match qs with
    | None    -> t_or (t_elimT_ind `Ind) t_elim tc
    | Some qs ->
        let qs = { fp_head = FPNamed (qs, None); fp_args = []; } in
        process_elimT qs tc
  in
    try
      FApi.t_last doelim (process_generalize pe tc)
    with EcCoreGoal.InvalidGoalShape ->
      tc_error !!tc "don't know what to eliminate"

(* -------------------------------------------------------------------- *)
let process_case gp tc =
  let module E = struct exception LEMFailure end in

  try
    match gp with
    | [`Form (None, pf)] ->
        let env = FApi.tc1_env tc in

        let f =
          try  TTC.process_formula (FApi.tc1_hyps tc) pf
          with TT.TyError _ | LocError (_, TT.TyError _) -> raise E.LEMFailure
        in
          if not (EcReduction.EqTest.for_type env f.f_ty tbool) then
            raise E.LEMFailure;
          t_seq
            (t_case f)
            (t_simplify_with_info EcReduction.betaiota_red)
            tc

    | _ -> raise E.LEMFailure

  with E.LEMFailure ->
    try
      FApi.t_last
        (t_or (t_elimT_ind `Case) t_elim)
        (process_generalize gp tc)
    with EcCoreGoal.InvalidGoalShape ->
      tc_error !!tc "don't known what to eliminate"

(* -------------------------------------------------------------------- *)
let process_exists args (tc : tcenv1) =
  let hyps = FApi.tc1_hyps tc in
  let pte  = (TTC.unienv_of_hyps hyps, EcMatching.MEV.empty) in
  let pte  = PT.ptenv !!tc (FApi.tc1_hyps tc) pte in

  let for1 concl arg =
    match TTC.destruct_exists hyps concl with
    | None -> tc_error !!tc "not an existential"
    | Some (`Exists (x, xty, f)) ->
        let arg =
          match xty with
          | GTty    _ -> trans_pterm_arg_value pte arg
          | GTmem   _ -> trans_pterm_arg_mem   pte arg
          | GTmodty _ -> trans_pterm_arg_mod   pte arg
        in
          PT.check_pterm_arg pte (x, xty) f arg.ptea_arg
  in

  let _concl, args = List.map_fold for1 (FApi.tc1_goal tc) args in

  if not (PT.can_concretize pte) then
    tc_error !!tc "cannot infer all placeholders";

  let pte  = PT.concretize_env pte in
  let args = List.map (PT.concretize_e_arg pte) args in

  EcLowGoal.t_exists_intro_s args tc

(* -------------------------------------------------------------------- *)
let process_congr tc =
  let (hyps, concl) = FApi.tc1_flat tc in

  if not (EcFol.is_eq concl) then
    tc_error !!tc "goal must be an equality";

  let (f1, f2) = EcFol.destr_eq concl in

  match f1.f_node, f2.f_node with
  | Fapp (o1, a1), Fapp (o2, a2)
      when    EcReduction.is_alpha_eq hyps o1 o2
           && List.length a1 = List.length a2 ->

      let tt1 = t_congr (o1, o2) ((List.combine a1 a2), f1.f_ty) in
      let tt2 = t_logic_trivial in
      FApi.t_seq tt1 tt2 tc

  | Ftuple _, Ftuple _ ->
      FApi.t_seqs [t_split; t_logic_trivial] tc

  | _, _ when EcReduction.is_alpha_eq hyps f1 f2 ->
      EcLowGoal.t_reflex tc

  | _, _ -> tacuerror "not a congruence"

(* -------------------------------------------------------------------- *)
let process_algebra mode kind eqs (tc : tcenv1) =
  let (env, hyps, concl) = FApi.tc1_eflat tc in

  if not (EcAlgTactic.is_module_loaded env) then
    tacuerror "ring/field cannot be used when AlgTactic is not loaded";

  let (ty, f1, f2) =
    match sform_of_form concl with
    | SFeq (f1, f2) -> (f1.f_ty, f1, f2)
    | _ -> tacuerror "conclusion must be an equation"
  in

  let eqs =
    let eq1 { pl_desc = x } =
      match LDecl.has_hyp x hyps with
      | false -> tacuerror "cannot find equation referenced by `%s'" x
      | true  -> begin
        match sform_of_form (snd (LDecl.lookup_hyp x hyps)) with
        | SFeq (f1, f2) ->
            if not (EcReduction.EqTest.for_type env ty f1.f_ty) then
              tacuerror "assumption `%s' is not an equation over the right type" x;
            (f1, f2)
        | _ -> tacuerror "assumption `%s' is not an equation" x
      end
    in List.map eq1 eqs
  in

  let tparams = (LDecl.tohyps hyps).h_tvar in

  let tactic =
    match
      match mode, kind with
      | `Simpl, `Ring  -> `Ring  EcAlgTactic.t_ring_simplify
      | `Simpl, `Field -> `Field EcAlgTactic.t_field_simplify
      | `Solve, `Ring  -> `Ring  EcAlgTactic.t_ring
      | `Solve, `Field -> `Field EcAlgTactic.t_field
    with
    | `Ring t ->
        let r =
          match TT.get_ring (tparams, ty) env with
          | None   -> tacuerror "cannot find a ring structure"
          | Some r -> r
        in t r eqs (f1, f2)
    | `Field t ->
        let r =
          match TT.get_field (tparams, ty) env with
          | None   -> tacuerror "cannot find a field structure"
          | Some r -> r
        in t r eqs (f1, f2)
  in

  tactic tc
