(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
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
  tt_provers   : EcParsetree.pprover_infos -> EcProvers.prover_infos;
  tt_smtmode   : [`Admit | `Strict | `Standard | `Report];
  tt_implicits : bool;
  tt_oldip     : bool;
  tt_redlogic  : bool;
}

type engine = ptactic_core -> FApi.backward

(* -------------------------------------------------------------------- *)
let t_simplify_lg ?target ?delta (ttenv, logic) (tc : tcenv1) =
  let logic =
    match logic with
    | `Default -> if ttenv.tt_redlogic then `Full else `ProductCompat
    | `Variant -> if ttenv.tt_redlogic then `ProductCompat else `Full
  in t_simplify ?target ?delta ~logic:(Some logic) tc

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
let process_change fp (tc : tcenv1) =
  let fp = TTC.tc1_process_formula tc fp in
  FApi.tcenv_of_tcenv1 (t_change fp tc)

(* -------------------------------------------------------------------- *)
let process_simplify_info ri (tc : tcenv1) =
  let env, hyps, _ = FApi.tc1_eflat tc in

  let do1 (sop, sid) ps =
    match ps.pl_desc with
    | ([], s) when LDecl.has_name s hyps ->
        let id = fst (LDecl.by_name s hyps) in
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

  {
    EcReduction.beta    = ri.pbeta;
    EcReduction.delta_p = delta_p;
    EcReduction.delta_h = delta_h;
    EcReduction.zeta    = ri.pzeta;
    EcReduction.iota    = ri.piota;
    EcReduction.eta     = ri.peta;
    EcReduction.logic   = if ri.plogic then Some `Full else None;
    EcReduction.modpath = ri.pmodpath;
    EcReduction.user    = ri.puser;
  }

(*-------------------------------------------------------------------- *)
let process_simplify ri (tc : tcenv1) =
  t_simplify_with_info (process_simplify_info ri tc) tc

(* -------------------------------------------------------------------- *)
let process_cbv ri (tc : tcenv1) =
  t_cbv_with_info (process_simplify_info ri tc) tc

(* -------------------------------------------------------------------- *)
let process_smt ?loc (ttenv : ttenv) pi (tc : tcenv1) =
  let pi = ttenv.tt_provers pi in

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
    if not (LDecl.has_name (unloc s) hyps) then
      tc_lookup_error !!tc ~loc:s.pl_loc `Local ([], unloc s);
    fst (LDecl.by_name (unloc s) hyps)
  in

  try  t_clears (List.map toid symbols) tc
  with (ClearError _) as err -> tc_error_exn !!tc err

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
      match LDecl.hyp_exists x hyps with
      | false -> tacuerror "cannot find equation referenced by `%s'" x
      | true  -> begin
        match sform_of_form (snd (LDecl.hyp_by_name x hyps)) with
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

(* -------------------------------------------------------------------- *)
let t_apply_prept pt tc =
  EcLowGoal.Apply.t_apply_bwd_r (pt_of_prept tc pt) tc

(* -------------------------------------------------------------------- *)
module LowRewrite = struct
  type error =
  | LRW_NotAnEquation
  | LRW_NothingToRewrite
  | LRW_InvalidOccurence
  | LRW_CannotInfer
  | LRW_IdRewriting

  exception RewriteError of error

  let rec find_rewrite_patterns ~inpred (dir : rwside) pt =
    let hyps = pt.PT.ptev_env.PT.pte_hy in
    let env  = LDecl.toenv hyps in
    let pt   = { pt with ptev_ax = snd (PT.concretize pt) } in
    let ptc  = { pt with ptev_env = EcProofTerm.copy pt.ptev_env } in
    let ax   = pt.ptev_ax in

    let base ax =
      match EcFol.sform_of_form ax with
      | EcFol.SFeq  (f1, f2) -> Some (pt, `Eq, (f1, f2))
      | EcFol.SFiff (f1, f2) -> Some (pt, `Eq, (f1, f2))

      | EcFol.SFnot f ->
          let pt' = pt_of_global_r pt.ptev_env LG.p_negeqF [] in
          let pt' = apply_pterm_to_arg_r pt' (PVAFormula f) in
          let pt' = apply_pterm_to_arg_r pt' (PVASub pt) in
          Some (pt', `Eq, (f, f_false))

      | _ -> None
    in

    match base ax with
    | Some x -> [x]

    | _ -> begin
      let ptb = Lazy.from_fun (fun () ->
        let pt1 =
          if dir = `LtoR then
            if   ER.EqTest.for_type env ax.f_ty tbool
            then Some (ptc, `Bool, (ax, f_true))
            else None
          else None
        and pt2 = obind base
          (EcReduction.h_red_opt EcReduction.full_red hyps ax)
        in (otolist pt1) @ (otolist pt2)) in

        let rec doit reduce =
          match TTC.destruct_product ~reduce hyps ax with
          | None -> begin
             if reduce then Lazy.force ptb else
               let pts = doit true in
               if inpred then pts else (Lazy.force ptb) @ pts
            end

          | Some _ ->
             let pt = EcProofTerm.apply_pterm_to_hole pt in
             find_rewrite_patterns ~inpred:(inpred || reduce) dir pt

        in doit false
      end

  let find_rewrite_patterns = find_rewrite_patterns ~inpred:false

  let t_rewrite_r ?(mode = `Full) ?target (s, o) pt tc =
    let hyps, tgfp = FApi.tc1_flat ?target tc in

    let modes =
      match mode with
      | `Full  -> [{ k_keyed = true; k_conv = false };
                   { k_keyed = true; k_conv =  true };]
      | `Light -> [{ k_keyed = true; k_conv = false }] in

    let for1 (pt, mode, (f1, f2)) =
      let fp, tp = match s with `LtoR -> f1, f2 | `RtoL -> f2, f1 in
      let subf, occmode =
        (try
           PT.pf_find_occurence_lazy pt.PT.ptev_env ~modes ~ptn:fp tgfp
         with
         | PT.FindOccFailure `MatchFailure ->
             raise (RewriteError LRW_NothingToRewrite)
         | PT.FindOccFailure `IncompleteMatch ->
             raise (RewriteError LRW_CannotInfer)) in

      if not occmode.k_keyed then begin
        let tp = PT.concretize_form pt.PT.ptev_env tp in
        if EcReduction.is_conv hyps fp tp then
          raise (RewriteError LRW_IdRewriting);
      end;

      let pt   = fst (PT.concretize pt) in
      let cpos =
        try  FPosition.select_form
               ~xconv:`AlphaEq ~keyed:occmode.k_keyed
               hyps o subf tgfp
        with InvalidOccurence -> raise (RewriteError (LRW_InvalidOccurence))
      in

      EcLowGoal.t_rewrite
        ~keyed:occmode.k_keyed ?target ~mode pt (s, Some cpos) tc in

    let rec do_first = function
      | [] -> raise (RewriteError LRW_NothingToRewrite)

      | (pt, mode, (f1, f2)) :: pts ->
           try  for1 (pt, mode, (f1, f2))
           with RewriteError (LRW_NothingToRewrite | LRW_IdRewriting) ->
             do_first pts
    in

    let pts = find_rewrite_patterns s pt in

    if List.is_empty pts then
      raise (RewriteError LRW_NotAnEquation);
    do_first (List.rev pts)

  let t_rewrite ?target (s, o) pt (tc : tcenv1) =
    let hyps   = FApi.tc1_hyps ?target tc in
    let pt, ax = EcLowGoal.LowApply.check `Elim pt (`Hyps (hyps, !!tc)) in
    let ptenv  = ptenv_of_penv hyps !!tc in

    t_rewrite_r ?target (s, o)
      { ptev_env = ptenv; ptev_pt = pt; ptev_ax = ax; }
      tc

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
    in t_do_r ~focus:0 `Maybe None (t_ors (List.map try1 pts)) !@tc
end

let t_rewrite_prept info pt tc =
  LowRewrite.t_rewrite_r info (pt_of_prept tc pt) tc

(* -------------------------------------------------------------------- *)
let process_solve ?bases ?depth (tc : tcenv1) =
  match FApi.t_try_base (EcLowGoal.t_solve ~canfail:false ?bases ?depth) tc with
  | `Failure _ ->
      tc_error (FApi.tc1_penv tc) "[solve]: cannot close goal"
  | `Success tc ->
      tc

(* -------------------------------------------------------------------- *)
let process_trivial (tc : tcenv1) =
  EcPhlAuto.t_pl_trivial tc

(* -------------------------------------------------------------------- *)
let process_crushmode d =
  d.cm_simplify, if d.cm_solve then Some process_trivial else None

(* -------------------------------------------------------------------- *)
let process_done tc =
  let tc = process_trivial tc in

  if not (FApi.tc_done tc) then
    tc_error (FApi.tc_penv tc) "[by]: cannot close goals";
  tc

(* -------------------------------------------------------------------- *)
let process_apply_bwd ~implicits mode (ff : ppterm) (tc : tcenv1) =
  let pt = PT.tc1_process_full_pterm ~implicits tc ff in

  try
    let aout = EcLowGoal.Apply.t_apply_bwd_r pt tc in

    match mode with
    | `Apply -> aout
    | `Exact ->
        let aout = FApi.t_onall process_trivial aout in
        if not (FApi.tc_done aout) then
          tc_error !!tc "cannot close goal";
        aout

  with (EcLowGoal.Apply.NoInstance _) as err ->
    tc_error_exn !!tc err

(* -------------------------------------------------------------------- *)
let process_apply_fwd ~implicits (pe, hyp) tc =
  let module E = struct exception NoInstance end in

  let hyps = FApi.tc1_hyps tc in

  if not (LDecl.hyp_exists (unloc hyp) hyps) then
    tc_error !!tc "unknown hypothesis: %s" (unloc hyp);

  let hyp, fp = LDecl.hyp_by_name (unloc hyp) hyps in
  let pte = PT.tc1_process_full_pterm ~implicits tc pe in

  try
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

    let (pte, cutf) = instantiate pte in
    let pt = fst (PT.concretize pte) in
    let pt = { pt with pt_args = pt.pt_args @ [palocal hyp]; } in
    let cutf = PT.concretize_form pte.PT.ptev_env cutf in

    FApi.t_last
      (FApi.t_seq (t_clear hyp) (t_intros_i [hyp]))
      (t_cutdef pt cutf tc)

  with E.NoInstance ->
    tc_error_lazy !!tc
      (fun fmt ->
        let ppe = EcPrinting.PPEnv.ofenv (FApi.tc1_env tc) in
        Format.fprintf fmt
          "cannot apply (in %a) the given proof-term for:\n\n%!"
          (EcPrinting.pp_local ppe) hyp;
        Format.fprintf fmt
          "  @[%a@]" (EcPrinting.pp_form ppe) pte.PT.ptev_ax)

(* -------------------------------------------------------------------- *)
let process_apply_top tc =
  let hyps, concl = FApi.tc1_flat tc in

  match TTC.destruct_product hyps concl with
  | Some (`Imp _) -> begin
     let h = LDecl.fresh_id hyps "h" in

     try
       EcLowGoal.t_intros_i_seq ~clear:true [h]
         (EcLowGoal.Apply.t_apply_bwd { pt_head = PTLocal h; pt_args = []} )
         tc
     with (EcLowGoal.Apply.NoInstance _) as err ->
       tc_error_exn !!tc err
    end

  | _ -> tc_error !!tc "no top assumption"

(* -------------------------------------------------------------------- *)
let process_rewrite1_core ?mode ?(close = true) ?target (s, o) pt tc =
  let o = norm_rwocc o in

  try
    let tc = LowRewrite.t_rewrite_r ?mode ?target (s, o) pt tc in
    let cl = fun tc ->
      if EcFol.f_equal f_true (FApi.tc1_goal tc) then
        t_true tc
      else t_id tc
    in if close then FApi.t_last cl tc else tc
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
      | LowRewrite.LRW_IdRewriting ->
          tc_error !!tc "refuse to perform an identity rewriting"

(* -------------------------------------------------------------------- *)
let process_delta ?target (s, o, p) tc =
  let env, hyps, concl = FApi.tc1_eflat tc in
  let o = norm_rwocc o in

  let idtg, target =
    match target with
    | None   -> (None, concl)
    | Some h -> fst_map some (LDecl.hyp_by_name (unloc h) hyps)
  in

  match unloc p with
  | PFident ({ pl_desc = ([], x) }, None)
      when s = `LtoR && EcUtils.is_none o ->

    let check_op = fun p -> sym_equal (EcPath.basename p) x in
    let check_id = fun y -> sym_equal (EcIdent.name y) x in
    let target = EcReduction.simplify
      { EcReduction.no_red with
          EcReduction.delta_p = check_op;
          EcReduction.delta_h = check_id; }
      hyps target

    in FApi.tcenv_of_tcenv1 (t_change ?target:idtg target tc)

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
        | EcDecl.OB_oper (Some (EcDecl.OP_Plain (e, _))) ->
            (snd p, op.EcDecl.op_tparams, form_of_expr EcFol.mhr e, args)
        | EcDecl.OB_pred (Some (EcDecl.PR_Plain f)) ->
            (snd p, op.EcDecl.op_tparams, f, args)
        | _ ->
            tc_error !!tc "the operator cannot be unfolded"
    end

    | SFlocal x when LDecl.can_unfold x hyps ->
        ([], [], LDecl.unfold x hyps, [])

    | SFother { f_node = Fapp ({ f_node = Flocal x }, args) }
        when LDecl.can_unfold x hyps ->
        ([], [], LDecl.unfold x hyps, args)

    | _ -> tc_error !!tc "not headed by an operator/predicate"

  in

  let na = List.length args in

  match s with
  | `LtoR -> begin
    let matches =
      try  ignore (PT.pf_find_occurence ptenv ~ptn:p target); true
      with PT.FindOccFailure _ -> false
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
          try  FPosition.select ?o test target
          with InvalidOccurence ->
            tc_error !!tc "invalid occurences selector"
      in

      let target =
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
                with EcEnv.NotReducible -> body
            end

            | SFlocal _ -> begin
                assert (tparams = []);
                let body = f_app body args topfp.f_ty in
                  try  EcReduction.h_red EcReduction.beta_red hyps body
                  with EcEnv.NotReducible -> body
            end

            | _ -> assert false)
          target
      in
        FApi.tcenv_of_tcenv1 (t_change ?target:idtg target tc)
    end else t_id tc
  end

  | `RtoL ->
    let fp =
      (* FIXME: TC HOOK *)
      let subst = EcTypes.Tvar.init (List.map fst tparams) tvi in
      let body  = EcFol.Fsubst.subst_tvar subst body in
      let fp    = f_app body args p.f_ty in
        try  EcReduction.h_red EcReduction.beta_red hyps fp
        with EcEnv.NotReducible -> fp
    in

    let matches =
      try  ignore (PT.pf_find_occurence ptenv ~ptn:fp target); true
      with PT.FindOccFailure _ -> false
    in

    if matches then begin
      let p    = concretize_form ptenv p  in
      let fp   = concretize_form ptenv fp in
      let cpos =
        try  FPosition.select_form hyps o fp target
        with InvalidOccurence ->
          tc_error !!tc "invalid occurences selector"
      in

      let target = FPosition.map cpos (fun _ -> p) target in
        FApi.tcenv_of_tcenv1 (t_change ?target:idtg target tc)
    end else t_id tc

(* -------------------------------------------------------------------- *)
let rec process_rewrite1_r ttenv ?target ri tc =
  let implicits = ttenv.tt_implicits in

  match unloc ri with
  | RWDone simpl ->
      let tt =
        match simpl with
        | Some logic ->
           t_simplify_lg ?target:None ~delta:false (ttenv, logic)
        | None -> t_id
      in FApi.t_seq tt process_trivial tc

  | RWSimpl logic ->
      let hyps   = FApi.tc1_hyps tc in
      let target = target |> omap (fst |- LDecl.hyp_by_name^~ hyps |- unloc) in
      t_simplify_lg ?target ~delta:false (ttenv, logic) tc

  | RWDelta ((s, r, o), p) -> begin
      let do1 tc = process_delta ?target (s, o, p) tc in

      match r with
      | None -> do1 tc
      | Some (b, n) -> t_do b n do1 tc
  end

  | RWRw (((s : rwside), r, o), pts) -> begin
      let do1 (mode : [`Full | `Light]) ((subs : rwside), pt) tc =
        let hyps   = FApi.tc1_hyps tc in
        let target = target |> omap (fst |- LDecl.hyp_by_name^~ hyps |- unloc) in
        let hyps   = FApi.tc1_hyps ?target tc in

        let theside =
          match s, subs with
          | `LtoR, _     -> (subs  :> rwside)
          | _    , `LtoR -> (s     :> rwside)
          | `RtoL, `RtoL -> (`LtoR :> rwside) in

        let is_baserw p tc =
          EcEnv.BaseRw.is_base p.pl_desc (FApi.tc1_env tc) in

        match pt with
        | { fp_head = FPNamed (p, None); fp_args = []; }
              when pt.fp_mode = `Implicit && is_baserw p tc
        ->
          let env = FApi.tc1_env tc in
          let ls  = snd (EcEnv.BaseRw.lookup p.pl_desc env) in
          let ls  = EcPath.Sp.elements ls in

          let do1 lemma tc =
            let pt = PT.pt_of_uglobal !!tc hyps lemma in
              process_rewrite1_core ~mode ?target (theside, o) pt tc in
            t_ors (List.map do1 ls) tc

        | { fp_head = FPNamed (p, None); fp_args = []; }
              when pt.fp_mode = `Implicit
        ->
          let env = FApi.tc1_env tc in
          let pt  =
            PT.process_full_pterm ~implicits
              (PT.ptenv_of_penv hyps !!tc) pt
          in

          if    is_ptglobal pt.PT.ptev_pt.pt_head
             && List.is_empty pt.PT.ptev_pt.pt_args
          then begin
            let ls = EcEnv.Ax.all ~name:(unloc p) env in

            let do1 (lemma, _) tc =
              let pt = PT.pt_of_uglobal !!tc hyps lemma in
                process_rewrite1_core ~mode ?target (theside, o) pt tc in
              t_ors (List.map do1 ls) tc
          end else
            process_rewrite1_core ~mode ?target (theside, o) pt tc

        | _ ->
          let pt =
            PT.process_full_pterm ~implicits
              (PT.ptenv_of_penv hyps !!tc) pt
          in process_rewrite1_core ~mode ?target (theside, o) pt tc
        in

      let doall mode tc = t_ors (List.map (do1 mode) pts) tc in

      match r with
      | None ->
          doall `Full tc
      | Some (`Maybe, None) ->
          t_seq
            (t_do `Maybe (Some 1) (doall `Full))
            (t_do `Maybe None (doall `Light))
            tc
      | Some (b, n) ->
          t_do b n (doall `Full) tc
  end

  | RWPr (x, f) -> begin
      if EcUtils.is_some target then
        tc_error !!tc "cannot rewrite Pr[] in local assumptions";
      EcPhlPrRw.t_pr_rewrite (unloc x, f) tc
  end

  | RWSmt (false, info) ->
     process_smt ~loc:ri.pl_loc ttenv info tc

  | RWSmt (true, info) ->
     t_or process_done (process_smt ~loc:ri.pl_loc ttenv info) tc

  | RWApp fp -> begin
      let implicits = ttenv.tt_implicits in
      match target with
      | None -> process_apply_bwd ~implicits `Apply fp tc
      | Some target -> process_apply_fwd ~implicits (fp, target) tc
    end

  | RWTactic `Ring ->
      process_algebra `Solve `Ring [] tc

  | RWTactic `Field ->
      process_algebra `Solve `Field [] tc

(* -------------------------------------------------------------------- *)
let rec process_rewrite1 ttenv ?target ri tc =
  EcCoreGoal.reloc (loc ri) (process_rewrite1_r ttenv ?target ri) tc

(* -------------------------------------------------------------------- *)
let process_rewrite ttenv ?target ri tc =
  let do1 tc gi (fc, ri) =
    let ngoals = FApi.tc_count tc in
    let dorw   = fun i tc ->
      if   gi = 0 || (i+1) = ngoals
      then process_rewrite1 ttenv ?target ri tc
      else process_rewrite1 ttenv ri tc
    in

    match fc |> omap ((process_tfocus tc) |- unloc) with
    | None    -> FApi.t_onalli dorw tc
    | Some fc -> FApi.t_onselecti fc dorw tc

  in
  List.fold_lefti do1 (tcenv_of_tcenv1 tc) ri

(* -------------------------------------------------------------------- *)
let process_elimT qs tc =
  let noelim () = tc_error !!tc "cannot recognize elimination principle" in

  let (hyps, concl) = FApi.tc1_flat tc in

  let (pf, pfty, _concl) =
    match TTC.destruct_product hyps concl with
    | Some (`Forall (x, GTty xty, concl)) -> (x, xty, concl)
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
        with MatchFailure -> try
          PT.pf_form_match ~mode:fmdelta pte.PT.ptev_env ~ptn:f2 fp;
          (pte, ids, f1, `IffRL (f1, f2))
        with MatchFailure ->
          raise E.NoInstance
    end
  in

  try
    match TTC.destruct_product (tc1_hyps tc) (FApi.tc1_goal tc) with
    | None -> raise E.NoTopAssumption

    | Some (`Forall _) ->
      process_elimT pe tc

    | Some (`Imp (f1, _)) when pe.fp_head = FPCut None ->
        let hyps = FApi.tc1_hyps tc in
        let hid  = LDecl.fresh_id hyps "h" in
        let hqs  = mk_loc _dummy ([], EcIdent.name hid) in
        let pe   = { pe with fp_head = FPNamed (hqs, None) } in

        t_intros_i_seq ~clear:true [hid]
          (fun tc ->
            let pe = PT.tc1_process_full_pterm tc pe in
            let regen =
              if PT.can_concretize pe.PT.ptev_env then [] else

              snd (List.fold_left_map (fun f1 arg ->
                let pre, f1 =
                  match oget (TTC.destruct_product (tc1_hyps tc) f1) with
                  | `Imp    (_, f1)      -> (None, f1)
                  | `Forall (x, xty, f1) ->
                    let aout =
                      match xty with GTty ty -> Some (x, ty) | _ -> None
                    in (aout, f1)
                in

                let module E = struct exception Bailout end in

                try
                  let v =
                    match arg with
                    | PAFormula { f_node = Flocal x } ->
                        let meta =
                          let env = !(pe.PT.ptev_env.pte_ev) in
                          MEV.mem x `Form env && not (MEV.isset x `Form env) in

                        if not meta then raise E.Bailout;

                        let y, yty =
                          let CPTEnv subst = PT.concretize_env pe.PT.ptev_env in
                          snd_map subst.fs_ty (oget pre) in
                        let fy = EcIdent.fresh y in

                        pe.PT.ptev_env.pte_ev := MEV.set
                          x (`Form (f_local fy yty)) !(pe.PT.ptev_env.pte_ev);
                        (fy, yty)

                    | _ ->
                        raise E.Bailout
                  in (f1, Some v)

                with E.Bailout -> (f1, None)
              ) f1 pe.PT.ptev_pt.pt_args)
            in

            let regen = List.pmap (fun x -> x) regen in
            let bds   = List.map (fun (x, ty) -> (x, GTty ty)) regen in

            if not (PT.can_concretize pe.PT.ptev_env) then
              tc_error !!tc "cannot infer all placeholders";

            let pt, ax = snd_map (f_forall bds) (PT.concretize pe) in
            t_first (fun subtc ->
              let regen = List.fst regen in
              let ttcut tc =
                t_onall
                  (EcLowGoal.t_generalize_hyps ~clear:`Yes regen)
                  (EcLowGoal.t_apply pt tc) in
              t_intros_i_seq regen ttcut subtc
            ) (t_cut ax tc)
          ) tc

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

            | `IffRL (f1, f2) ->
                let vpte = PT.pt_of_global_r pte.PT.ptev_env LG.p_iff_rl [] in
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
module IntroState : sig
  type state
  type action = [ `Revert | `Dup | `Clear ]

  val create  : unit -> state
  val push    : ?name:symbol -> action -> EcIdent.t -> state -> unit
  val listing : state -> ([`Gen of genclear | `Clear] * EcIdent.t) list
  val naming  : state -> (EcIdent.t -> symbol option)
end = struct
  type state = {
    mutable torev  : ([`Gen of genclear | `Clear] * EcIdent.t) list;
    mutable naming : symbol option Mid.t;
  }

  and action = [ `Revert | `Dup | `Clear ]

  let create () =
    { torev = []; naming = Mid.empty; }

  let push ?name action id st =
    let map =
      Mid.change (function
      | None   -> Some name
      | Some _ -> assert false)
      id st.naming
    and action =
      match action with
      | `Revert -> `Gen `TryClear
      | `Dup    -> `Gen `NoClear
      | `Clear  -> `Clear
    in
      st.torev  <- (action, id) :: st.torev;
      st.naming <- map

  let listing (st : state) =
    List.rev st.torev

  let naming (st : state) (x : EcIdent.t) =
    Mid.find_opt x st.naming |> odfl None
end

(* -------------------------------------------------------------------- *)
exception IntroCollect of [
  `InternalBreak
]

exception CollectBreak
exception CollectCore of ipcore located

let rec process_mintros_1 ?(cf = true) ttenv pis gs =
  let module ST = IntroState in

  let mk_intro ids (hyps, form) =
    let (_, torev), ids =
      let rec compile (((hyps, form), torev) as acc) newids ids =
        match ids with [] -> (acc, newids) | s :: ids ->

        let rec destruct fp =
          match EcFol.sform_of_form fp with
          | SFquant (Lforall, (x, _)  , lazy fp) ->
              let name = EcIdent.name x in (name, Some name, `Named, fp)
          | SFlet (LSymbol (x, _), _, fp) ->
              let name = EcIdent.name x in (name, Some name, `Named, fp)
          | SFimp (_, fp) ->
              ("H", None, `Hyp, fp)
          | _ -> begin
            match EcReduction.h_red_opt EcReduction.full_red hyps fp with
            | None   -> ("_", None, `None, f_true)
            | Some f -> destruct f
          end
        in
        let name, revname, kind, form = destruct form in
        let revertid =
          if ttenv.tt_oldip then
            match unloc s with
            | `Revert      -> Some (Some false, EcIdent.create "_")
            | `Clear       -> Some (None      , EcIdent.create "_")
            | `Named s     -> Some (None      , EcIdent.create s)
            | `Anonymous a ->
               if   (a = Some None && kind = `None) || a = Some (Some 0)
               then None
               else Some (None, LDecl.fresh_id hyps name)
          else
            match unloc s with
            | `Revert      -> Some (Some false, EcIdent.create "_")
            | `Clear       -> Some (Some true , EcIdent.create "_")
            | `Named s     -> Some (None      , EcIdent.create s)
            | `Anonymous a ->
               match a, kind with
               | Some None, `None ->
                  None
               | (Some (Some 0), _) ->
                  None
               | _, `Named ->
                  Some (None, LDecl.fresh_id hyps ("`" ^ name))
               | _, _ ->
                  Some (None, LDecl.fresh_id hyps "_")
        in

        match revertid with
        | Some (revert, id) ->
            let id     = mk_loc s.pl_loc id in
            let hyps   = LDecl.add_local id.pl_desc (LD_var (tbool, None)) hyps in
            let revert = revert |> omap (fun b -> if b then `Clear else `Revert) in
            let torev  = revert
              |> omap (fun b -> (b, unloc id, revname) :: torev)
              |> odfl torev
            in

            let newids = Tagged (unloc id, Some id.pl_loc) :: newids in

            let ((hyps, form), torev), newids =
              match unloc s with
              | `Anonymous (Some None) when kind <> `None ->
                 compile ((hyps, form), torev) newids [s]
              | `Anonymous (Some (Some i)) when 1 < i ->
                 let s = mk_loc (loc s) (`Anonymous (Some (Some (i-1)))) in
                 compile ((hyps, form), torev) newids [s]
              | _ -> ((hyps, form), torev), newids

            in compile ((hyps, form), torev) newids ids

        | None -> compile ((hyps, form), torev) newids ids

      in snd_map List.rev (compile ((hyps, form), []) [] ids)

    in (List.rev torev, ids)
  in

  let rec collect intl acc core pis =
    let maybe_core () =
      let loc = EcLocation.mergeall (List.map loc core) in
      match core with
      | [] -> acc
      | _  -> mk_loc loc (`Core (List.rev core)) :: acc
    in

    match pis with
    | [] -> (maybe_core (), [])
    | { pl_loc = ploc } as pi :: pis ->
      try
        let ip =
          match unloc pi with
          | IPBreak ->
             if intl then raise (IntroCollect `InternalBreak);
             raise CollectBreak

          | IPCore     x -> raise (CollectCore (mk_loc (loc pi) x))
          | IPDup        -> `Dup
          | IPDone     x -> `Done x
          | IPSmt      x -> `Smt x
          | IPClear    x -> `Clear x
          | IPRw       x -> `Rw x
          | IPDelta    x -> `Delta x
          | IPView     x -> `View x
          | IPSubst    x -> `Subst x
          | IPSimplify x -> `Simpl x
          | IPCrush    x -> `Crush x

          | IPCase (mode, x) ->
              let subcollect = List.rev -| fst -| collect true [] [] in
              `Case (mode, List.map subcollect x)

          | IPSubstTop x -> `SubstTop x

        in collect intl (mk_loc ploc ip :: maybe_core ()) [] pis

      with
      | CollectBreak  -> (maybe_core (), pis)
      | CollectCore x -> collect intl acc (x :: core) pis

  in

  let collect pis = collect false [] [] pis in

  let rec intro1_core (st : ST.state) ids (tc : tcenv1) =
    let torev, ids = mk_intro ids (FApi.tc1_flat tc) in
    List.iter (fun (act, id, name) -> ST.push ?name act id st) torev;
    t_intros ids tc

  and intro1_dup (_ : ST.state) (tc : tcenv1) =
    try
      let pt = PT.pt_of_uglobal !!tc (FApi.tc1_hyps tc) LG.p_ip_dup in
      EcLowGoal.Apply.t_apply_bwd_r ~mode:fmrigid ~canview:false pt tc
    with EcLowGoal.Apply.NoInstance _ ->
      tc_error !!tc "no top-assumption to duplicate"

  and intro1_done (_ : ST.state) simplify (tc : tcenv1) =
    let t =
      match simplify with
      | Some x ->
         t_seq (t_simplify_lg ~delta:false (ttenv, x)) process_trivial
      | None -> process_trivial
    in t tc

  and intro1_smt (_ : ST.state) ((dn, pi) : _ * pprover_infos) (tc : tcenv1) =
    if dn then
      t_or process_done (process_smt ttenv pi) tc
    else process_smt ttenv pi tc

  and intro1_simplify (_ : ST.state) logic tc =
    t_simplify_lg ~delta:false (ttenv, logic) tc

  and intro1_clear (_ : ST.state) xs tc =
    process_clear xs tc

  and intro1_case (st : ST.state) nointro pis gs =
    let onsub gs =
      if List.is_empty pis then gs else begin
        if FApi.tc_count gs <> List.length pis then
          tc_error !$gs
            "not the right number of intro-patterns (got %d, expecting %d)"
            (List.length pis) (FApi.tc_count gs);
        t_sub (List.map (dointro1 st false) pis) gs
        end
    in

    let tc = t_ors [t_elimT_ind `Case; t_elim; t_elim_prind `Case] in
    let tc =
      fun g ->
        try  tc g
        with InvalidGoalShape ->
          tc_error !!g "invalid intro-pattern: nothing to eliminate"
    in

    if nointro && not cf then onsub gs else begin
      match pis with
      | [] -> t_onall tc gs
      | _  -> t_onall (fun gs -> onsub (tc gs)) gs
    end

  and intro1_full_case (st : ST.state)
    ((prind, delta), withor, (cnt : icasemode_full option)) pis tc
  =
    let module E = struct exception IterDone of tcenv end in

    let cnt = cnt |> odfl (`AtMost 1) in
    let red = if delta then `Full else `NoDelta in

    let t_case =
      let t_and, t_or =
        if prind then
          ((fun tc -> fst_map List.singleton (t_elim_iso_and ~reduce:red tc)),
           (fun tc -> t_elim_iso_or ~reduce:red tc))
        else
          ((fun tc -> ([2]   , t_elim_and ~reduce:red tc)),
           (fun tc -> ([1; 1], t_elim_or  ~reduce:red tc))) in
      let ts = if withor then [t_and; t_or] else [t_and] in
      fun tc -> FApi.t_or_map ts tc
    in

    let onsub gs =
      if List.is_empty pis then gs else begin
        if FApi.tc_count gs <> List.length pis then
          tc_error !$gs
            "not the right number of intro-patterns (got %d, expecting %d)"
            (List.length pis) (FApi.tc_count gs);
        t_sub (List.map (dointro1 st false) pis) gs
        end
    in

    let doit tc =
      let rec aux imax tc =
        if imax = Some 0 then t_id tc else

        try
          let ntop, tc = t_case tc in

          FApi.t_sublasts
            (List.map (fun i tc -> aux (omap ((+) (i-1)) imax) tc) ntop)
            tc
        with InvalidGoalShape ->
          let id = EcIdent.create "_" in
          try
            t_seq
              (aux (omap ((+) (-1)) imax))
              (t_generalize_hyps ~clear:`Yes [id])
              (EcLowGoal.t_intros_i_1 [id] tc)
          with
          | EcCoreGoal.TcError _ when EcUtils.is_some imax ->
              tc_error !!tc "not enough top-assumptions"
          | EcCoreGoal.TcError _ ->
              t_id tc
      in

      match cnt with
      | `AtMost cnt -> aux (Some (max 1 cnt)) tc
      | `AsMuch     -> aux None tc
    in

    if List.is_empty pis then doit tc else onsub (doit tc)

  and intro1_rw (_ : ST.state) (o, s) tc =
    let h = EcIdent.create "_" in
    let rwt tc =
      let pt = PT.pt_of_hyp !!tc (FApi.tc1_hyps tc) h in
      process_rewrite1_core ~close:false (s, o) pt tc
    in t_seqs [t_intros_i [h]; rwt; t_clear h] tc

  and intro1_unfold (_ : ST.state) (s, o) p tc =
    process_delta (s, o, p) tc

  and intro1_view (_ : ST.state) pe tc =
    process_view1 pe tc

  and intro1_subst (_ : ST.state) d (tc : tcenv1) =
    try
      t_intros_i_seq ~clear:true [EcIdent.create "_"]
        (EcLowGoal.t_subst ~clear:false ~tside:(d :> tside))
        tc
    with InvalidGoalShape ->
      tc_error !!tc "nothing to substitute"

  and intro1_subst_top (_ : ST.state) (omax, osd) (tc : tcenv1) =
    let t_subst eqid =
      let sk1  = { empty_subst_kind with sk_local = true ; } in
      let sk2  = {  full_subst_kind with sk_local = false; } in
      let side = `All osd in
      FApi.t_or
        (t_subst ~tside:side ~kind:sk1 ~eqid)
        (t_subst ~tside:side ~kind:sk2 ~eqid)
    in

    let togen = ref [] in

    let rec doit i tc =
      match omax with Some max when i >= max -> tcenv_of_tcenv1 tc | _ ->

      try
        let id = EcIdent.create "_" in
        let tc = EcLowGoal.t_intros_i_1 [id] tc in
        FApi.t_switch (t_subst id) ~ifok:(doit (i+1))
          ~iffail:(fun tc -> togen := id :: !togen; doit (i+1) tc)
          tc
      with EcCoreGoal.TcError _ ->
        if is_some omax then
          tc_error !!tc "not enough top-assumptions";
        tcenv_of_tcenv1 tc in

    let tc = doit 0 tc in

    t_generalize_hyps
      ~clear:`Yes ~missing:true
      (List.rev !togen) (FApi.as_tcenv1 tc)

  and intro1_crush (_st : ST.state) (d : crushmode) (gs : tcenv1) =
    let delta, tsolve = process_crushmode d in
    FApi.t_or
      (EcPhlConseq.t_conseqauto ~delta ?tsolve)
      (EcLowGoal.t_crush ~delta ?tsolve)
      gs

  and dointro (st : ST.state) nointro pis (gs : tcenv) =
    match pis with [] -> gs | { pl_desc = pi; pl_loc = ploc } :: pis ->
      let nointro, gs =
        let rl x = EcCoreGoal.reloc ploc x in

        match pi with
        | `Core ids ->
            (false, rl (t_onall (intro1_core st ids)) gs)

        | `Dup ->
            (false, rl (t_onall (intro1_dup st)) gs)

        | `Done b ->
            (nointro, rl (t_onall (intro1_done st b)) gs)

        | `Smt pi ->
            (nointro, rl (t_onall (intro1_smt st pi)) gs)

        | `Simpl b ->
            (nointro, rl (t_onall (intro1_simplify st b)) gs)

        | `Clear xs ->
            (nointro, rl (t_onall (intro1_clear st xs)) gs)

        | `Case (`One, pis) ->
            (false, rl (intro1_case st nointro pis) gs)

        | `Case (`Full x, pis) ->
            (false, rl (t_onall (intro1_full_case st x pis)) gs)

        | `Rw (o, s, None) ->
            (false, rl (t_onall (intro1_rw st (o, s))) gs)

        | `Rw (o, s, Some i) ->
            (false, rl (t_onall (t_do `All i (intro1_rw st (o, s)))) gs)

        | `Delta ((o, s), p) ->
            (nointro, rl (t_onall (intro1_unfold st (o, s) p)) gs)

        | `View pe ->
            (false, rl (t_onall (intro1_view st pe)) gs)

        | `Subst (d, None) ->
            (false, rl (t_onall (intro1_subst st d)) gs)

        | `Subst (d, Some i) ->
            (false, rl (t_onall (t_do `All i (intro1_subst st d))) gs)

        | `SubstTop d ->
            (false, rl (t_onall (intro1_subst_top st d)) gs)

        | `Crush d ->
           (false, rl (t_onall (intro1_crush st d)) gs)

      in dointro st nointro pis gs

  and dointro1 st nointro pis tc =
    dointro st nointro pis (FApi.tcenv_of_tcenv1 tc) in

  try
    let st = ST.create () in
    let ip, pis = collect pis in
    let gs = dointro st true (List.rev ip) gs in
    let gs =
      let ls = ST.listing st in
      let gn = List.pmap (function (`Gen x, y) -> Some (x, y) | _ -> None) ls in
      let cl = List.pmap (function (`Clear, y) -> Some y | _ -> None) ls in

      t_onall (fun tc ->
        t_generalize_hyps_x
          ~missing:true ~naming:(ST.naming st)
           gn tc)
        (t_onall (t_clears cl) gs)
    in

    if List.is_empty pis then gs else
      gs |> t_onall (fun tc ->
        process_mintros_1 ~cf:true ttenv pis (FApi.tcenv_of_tcenv1 tc))

  with IntroCollect e -> begin
    match e with
    | `InternalBreak ->
         tc_error !$gs "cannot use internal break in intro-patterns"
  end

(* -------------------------------------------------------------------- *)
let process_intros_1 ?cf ttenv pis tc =
  process_mintros_1 ?cf ttenv pis (FApi.tcenv_of_tcenv1 tc)

(* -------------------------------------------------------------------- *)
let rec process_mintros ?cf ttenv pis tc =
  match pis with [] -> tc | pi :: pis ->
    let tc = process_mintros_1 ?cf ttenv pi tc in
    process_mintros ~cf:false ttenv pis tc

(* -------------------------------------------------------------------- *)
let process_intros ?cf ttenv pis tc =
  process_mintros ?cf ttenv pis (FApi.tcenv_of_tcenv1 tc)

(* -------------------------------------------------------------------- *)
let process_generalize1 ?(doeq = false) pattern (tc : tcenv1) =
  let env, hyps, concl = FApi.tc1_eflat tc in

  let onresolved ?(tryclear = true) pattern =
    let clear = if tryclear then `Yes else `No in

    match pattern with
    | `Form (occ, pf) -> begin
        match pf.pl_desc with
        | PFident ({pl_desc = ([], s)}, None)
            when not doeq && is_none occ && LDecl.has_name s hyps
          ->
            let id = fst (LDecl.by_name s hyps) in
            t_generalize_hyp ~clear id tc

        | _ ->
          let (ptenv, p) =
            let (ps, ue), p = TTC.tc1_process_pattern tc pf in
            let ev = MEV.of_idents (Mid.keys ps) `Form in
              (ptenv !!tc hyps (ue, ev), p)
          in

          (try  ignore (PT.pf_find_occurence ptenv ~ptn:p concl)
           with PT.FindOccFailure _ -> tc_error !!tc "cannot find an occurence");

          let p    = PT.concretize_form ptenv p in
          let occ  = norm_rwocc occ in
          let cpos =
            try  FPosition.select_form ~xconv:`AlphaEq hyps occ p concl
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
          let newconcl =
            if doeq then
              if EcReduction.EqTest.for_type env p.f_ty tbool then
                f_imps [f_iff p (f_local name p.f_ty)] newconcl
              else
                f_imps [f_eq p (f_local name p.f_ty)] newconcl
            else newconcl in
          let newconcl = f_forall [(name, GTty p.f_ty)] newconcl in
          let pt = { pt_head = PTCut newconcl; pt_args = [PAFormula p]; } in

          EcLowGoal.t_apply pt tc

    end

    | `ProofTerm fp -> begin
        match fp.fp_head with
        | FPNamed ({ pl_desc = ([], s) }, None)
            when LDecl.has_name s hyps && List.is_empty fp.fp_args
          ->
            let id = fst (LDecl.by_name s hyps) in
            t_generalize_hyp ~clear id tc

        | _ ->
          let pt = PT.tc1_process_full_pterm tc fp in
          if not (PT.can_concretize pt.PT.ptev_env) then
            tc_error !!tc "cannot infer all placeholders";
          let pt, ax = PT.concretize pt in
          t_cutdef pt ax tc
    end

    | `LetIn x ->
        let id =
          let binding =
            try  Some (LDecl.by_name (unloc x) hyps)
            with EcEnv.LDecl.LdeclError _ -> None in

            match binding  with
            | Some (id, LD_var (_, Some _)) -> id
            | _ ->
                let msg = "symbol must reference let-in" in
                tc_error ~loc:(loc x) !!tc "%s" msg

        in t_generalize_hyp ~clear ~letin:true id tc
  in

  match ffpattern_of_genpattern hyps pattern with
  | Some ff ->
     let tryclear =
       match pattern with
       | (`Form (None, { pl_desc = PFident _ })) -> true
       | _ -> false
     in onresolved ~tryclear (`ProofTerm ff)
  | None -> onresolved pattern

(* -------------------------------------------------------------------- *)
let process_generalize ?(doeq = false) patterns (tc : tcenv1) =
  try
    let patterns = List.mapi (fun i p ->
      process_generalize1 ~doeq:(doeq && i = 0) p) patterns in
    FApi.t_seqs (List.rev patterns) tc
  with (EcCoreGoal.ClearError _) as err ->
    tc_error_exn !!tc err

(* -------------------------------------------------------------------- *)
let rec process_mgenintros ?cf ttenv pis tc =
  match pis with [] -> tc | pi :: pis ->
    let tc =
      match pi with
      | `Ip  pi -> process_mintros_1 ?cf ttenv pi tc
      | `Gen gn ->
         t_onall (
           t_seqs [
               process_clear gn.pr_clear;
               process_generalize gn.pr_genp
           ]) tc
    in process_mgenintros ~cf:false ttenv pis tc

(* -------------------------------------------------------------------- *)
let process_genintros ?cf ttenv pis tc =
  process_mgenintros ?cf ttenv pis (FApi.tcenv_of_tcenv1 tc)

(* -------------------------------------------------------------------- *)
let process_move ?doeq views pr (tc : tcenv1) =
  t_seqs
    [process_clear pr.pr_clear;
     process_generalize ?doeq pr.pr_genp;
     process_view views]
    tc

(* -------------------------------------------------------------------- *)
let process_pose xsym bds o p (tc : tcenv1) =
  let (env, hyps, concl) = FApi.tc1_eflat tc in
  let o = norm_rwocc o in

  let (ptenv, p) =
    let ps  = ref Mid.empty in
    let ue  = TTC.unienv_of_hyps hyps in
    let (senv, bds) = EcTyping.trans_binding env ue bds in
    let p = EcTyping.trans_pattern senv ps ue p in
    let ev = MEV.of_idents (Mid.keys !ps) `Form in
    (ptenv !!tc hyps (ue, ev),
     f_lambda (List.map (snd_map gtty) bds) p)
  in

  let dopat =
    try  ignore (PT.pf_find_occurence ptenv ~ptn:p concl); true
    with PT.FindOccFailure _ ->
      if not (PT.can_concretize ptenv) then
        if not (EcMatching.MEV.filled !(ptenv.PT.pte_ev)) then
          tc_error !!tc "cannot find an occurence"
        else
          tc_error !!tc "%s - %s"
            "cannot find an occurence"
            "instantiate type variables manually"
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
type apply_t = EcParsetree.apply_info

let process_apply ~implicits ((infos, orv) : apply_t * prevert option) tc =
  let do_apply tc =
    match infos with
    | `ApplyIn (pe, tg) ->
        process_apply_fwd ~implicits (pe, tg) tc

    | `Apply (pe, mode) ->
        let for1 tc pe =
          t_last (process_apply_bwd ~implicits `Apply pe) tc in
        let tc = List.fold_left for1 (tcenv_of_tcenv1 tc) pe in
        if mode = `Exact then t_onall process_done tc else tc

    | `Top mode ->
        let tc = process_apply_top tc in
        if mode = `Exact then t_onall process_done tc else tc

  in

  t_seq
    (fun tc -> ofdfl
       (fun () -> t_id tc)
       (omap (fun rv -> process_move [] rv tc) orv))
    do_apply tc

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
type cutmode  = [`Have | `Suff]

let process_cut ?(mode = `Have) engine ttenv ((ip, phi, t) : cut_t) tc =
  let phi = TTC.tc1_process_formula tc phi in
  let tc  = EcLowGoal.t_cut phi tc in

  let applytc tc =
    t |> ofold (fun t tc ->
      let t = mk_loc (loc t) (Pby (Some (unloc t))) in
      t_onall (engine t) tc) (FApi.tcenv_of_tcenv1 tc)
  in

  match mode with
  | `Have ->
     FApi.t_first applytc
       (FApi.t_last (process_intros_1 ttenv ip) tc)

  | `Suff ->
     FApi.t_rotate `Left 1
       (FApi.t_on1 0 t_id ~ttout:applytc
         (FApi.t_last (process_intros_1 ttenv ip) tc))

(* -------------------------------------------------------------------- *)
type cutdef_t = intropattern * pcutdef

let process_cutdef ttenv (ip, pt) (tc : tcenv1) =
  let pt = {
      fp_mode = `Implicit;
      fp_head = FPNamed (pt.ptcd_name, pt.ptcd_tys);
      fp_args = pt.ptcd_args;
  } in

  let pt = PT.tc1_process_full_pterm tc pt in

  if not (PT.can_concretize pt.ptev_env) then
    tc_error !!tc "cannot infer all placeholders";

  let pt, ax = PT.concretize pt in

  FApi.t_sub
    [EcLowGoal.t_apply pt; process_intros_1 ttenv ip]
    (t_cut ax tc)

(* -------------------------------------------------------------------- *)
let process_left (tc : tcenv1) =
  try
    t_ors [EcLowGoal.t_left; EcLowGoal.t_or_intro_prind `Left] tc
  with InvalidGoalShape ->
    tc_error !!tc "cannot apply `left` on that goal"

(* -------------------------------------------------------------------- *)
let process_right (tc : tcenv1) =
  try
    t_ors [EcLowGoal.t_right; EcLowGoal.t_or_intro_prind `Right] tc
  with InvalidGoalShape ->
    tc_error !!tc "cannot apply `right` on that goal"

(* -------------------------------------------------------------------- *)
let process_split (tc : tcenv1) =
  try  t_ors [EcLowGoal.t_split; EcLowGoal.t_split_prind] tc
  with InvalidGoalShape ->
    tc_error !!tc "cannot apply `split` on that goal"

(* -------------------------------------------------------------------- *)
let process_elim (pe, qs) tc =
  let doelim tc =
    match qs with
    | None    -> t_or (t_elimT_ind `Ind) t_elim tc
    | Some qs ->
        let qs = {
            fp_mode = `Implicit;
            fp_head = FPNamed (qs, None);
            fp_args = [];
        } in process_elimT qs tc
  in
    try
      FApi.t_last doelim (process_move [] pe tc)
    with EcCoreGoal.InvalidGoalShape ->
      tc_error !!tc "don't know what to eliminate"

(* -------------------------------------------------------------------- *)
let process_case ?(doeq = false) gp tc =
  let module E = struct exception LEMFailure end in

  try
    match gp.pr_rev with
    | { pr_genp = [`Form (None, pf)] }
        when List.is_empty gp.pr_view ->

        let env = FApi.tc1_env tc in

        let f =
          try  TTC.process_formula (FApi.tc1_hyps tc) pf
          with TT.TyError _ | LocError (_, TT.TyError _) -> raise E.LEMFailure
        in
          if not (EcReduction.EqTest.for_type env f.f_ty tbool) then
            raise E.LEMFailure;
          begin
            match (fst (destr_app f)).f_node with
            | Fop (p, _) when EcEnv.Op.is_prind env p ->
               raise E.LEMFailure
            | _ -> ()
          end;
          t_seqs
            [process_clear gp.pr_rev.pr_clear; t_case f;
             t_simplify_with_info EcReduction.betaiota_red]
            tc

    | _ -> raise E.LEMFailure

  with E.LEMFailure ->
    try
      FApi.t_last
        (t_ors [t_elimT_ind `Case; t_elim; t_elim_prind `Case])
        (process_move ~doeq gp.pr_view gp.pr_rev tc)

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
  let (env, hyps, concl) = FApi.tc1_eflat tc in

  if not (EcFol.is_eq_or_iff concl) then
    tc_error !!tc "goal must be an equality or an equivalence";

  let ((f1, f2), iseq) =
    if   EcFol.is_eq concl
    then (EcFol.destr_eq  concl, true )
    else (EcFol.destr_iff concl, false) in

  match f1.f_node, f2.f_node with
  | Fapp (o1, a1), Fapp (o2, a2)
      when    EcReduction.is_alpha_eq hyps o1 o2
           && List.length a1 = List.length a2 ->

      let tt0 = if iseq then t_id else (fun tc ->
        let hyps = FApi.tc1_hyps tc in
        EcLowGoal.Apply.t_apply_bwd_r
          (PT.pt_of_uglobal !!tc hyps LG.p_eq_iff) tc) in
      let tt1 = t_congr (o1, o2) ((List.combine a1 a2), f1.f_ty) in
      let tt2 = t_logic_trivial in

      FApi.t_seqs [tt0; tt1; tt2] tc

  | Fif (_, { f_ty = cty }, _), Fif _ ->
     let tt0 tc =
       let hyps = FApi.tc1_hyps tc in
       EcLowGoal.Apply.t_apply_bwd_r
         (PT.pt_of_global !!tc hyps LG.p_if_congr [cty]) tc
     in FApi.t_seqs [tt0; t_logic_trivial] tc

  | Ftuple _, Ftuple _ when iseq ->
      FApi.t_seqs [t_split; t_logic_trivial] tc

  | Fproj (f1, i1), Fproj (f2, i2)
      when i1 = i2 && EcReduction.EqTest.for_type env f1.f_ty f2.f_ty
    -> EcCoreGoal.FApi.xmutate1 tc `CongrProj [f_eq f1 f2]

  | _, _ when iseq && EcReduction.is_alpha_eq hyps f1 f2 ->
      EcLowGoal.t_reflex tc

  | _, _ -> tacuerror "not a congruence"

(* -------------------------------------------------------------------- *)
let process_wlog ids wlog tc =
  let hyps, _ = FApi.tc1_flat tc in

  let toid s =
    if not (LDecl.has_name (unloc s) hyps) then
      tc_lookup_error !!tc ~loc:s.pl_loc `Local ([], unloc s);
    fst (LDecl.by_name (unloc s) hyps) in

  let ids = List.map toid ids in

  let gen =
    let wlog = TTC.tc1_process_formula tc wlog in
    let tc   = t_rotate `Left 1 (EcLowGoal.t_cut wlog tc) in
    let tc   = t_first (t_generalize_hyps ~clear:`Yes ids) tc in
    FApi.tc_goal tc
  in

  t_rotate `Left 1
    (t_first
       (t_seq (t_clears ids) (t_intros_i ids))
       (t_cut gen tc))
