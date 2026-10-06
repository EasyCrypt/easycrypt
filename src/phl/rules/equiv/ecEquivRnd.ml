(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcTypes
open EcModules
open EcFol
open EcAst
open EcEnv
open EcSubst

open EcMatching.Position
open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal

module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
type mkbij_t   = ty -> ty -> ts_inv
type semrndpos = (bool * codegap1) doption

(* Parameters of the two-sided equiv [rnd] rule: the bijection [f] between
   the sampled values and its inverse, instantiated at their types. Already
   typed, nothing to resolve: the same record is the rule argument and the
   node payload. *)
type equiv_rnd = {
  ern_f    : ts_inv;   (* f    : tyL -> tyR *)
  ern_finv : ts_inv;   (* finv : tyR -> tyL *)
}

(* Parameters of the one-sided equiv [rnd] rule: the side of the sampling. *)
type equiv_rnd_onesided = {
  eros_side : side;
}

type EcCoreGoal.rule +=
  | REquivRnd         of equiv_rnd
  | REquivRndOneSided of equiv_rnd_onesided

(* -------------------------------------------------------------------- *)
(* Weakest precondition of [xL <$ dL ~ xR <$ dR] for the relation [post],
   along the bijection [f] / [finv]:
        (forall xR, xR \in dR => xR = f (finv xR))
     /\ (forall xR, xR \in dR => mu1 dR xR = mu1 dL (finv xR))
     /\ (forall xL, xL \in dL =>
           f xL \in dR /\ xL = finv (f xL) /\ post[xL<1> := xL, xR<2> := f xL]) *)
let equiv_rnd_wp env ((lvL, muL), (lvR, muR)) (n : equiv_rnd) (post : ts_inv) =
  let ml, mr = post.ml, post.mr in
  let tyL = proj_distr_ty env (e_ty muL) in
  let tyR = proj_distr_ty env (e_ty muR) in
  let xL_id = EcIdent.create (symbol_of_lv lvL ^ "L")
  and xR_id = EcIdent.create (symbol_of_lv lvR ^ "R") in
  let xL  = {ml;mr;inv=f_local xL_id tyL} in
  let xR  = {ml;mr;inv=f_local xR_id tyR} in
  let muL = EcFol.ss_inv_of_expr ml muL in
  let muR = EcFol.ss_inv_of_expr mr muR in

  let f_app_simpl' ty f t = f_app_simpl f [t] ty in
  let f    t = map_ts_inv2 (f_app_simpl' tyR) n.ern_f t in
  let finv t = map_ts_inv2 (f_app_simpl' tyL) n.ern_finv t in

  let post = subst_form_lv_left env lvL xL post in
  let post = subst_form_lv_right env lvR (f xL) post in

  let muL = ss_inv_generalize_right muL mr in
  let muR = ss_inv_generalize_left muR ml in

  let cond_fbij      = map_ts_inv2 f_eq xL (finv (f xL)) in
  let cond_fbij_inv  = map_ts_inv2 f_eq xR (f (finv xR)) in

  let cond1 = map_ts_inv2 f_imp (map_ts_inv2 f_in_supp xR muR) cond_fbij_inv in
  let cond2 = map_ts_inv2 f_imp (map_ts_inv2 f_in_supp xR muR) (map_ts_inv2 f_eq (map_ts_inv2 f_mu_x muR xR) (map_ts_inv2 f_mu_x muL (finv xR))) in
  let cond3 = map_ts_inv f_andas [map_ts_inv2 f_in_supp (f xL) muR; cond_fbij; post] in
  let cond3 = map_ts_inv2 f_imp (map_ts_inv2 f_in_supp xL muL) cond3 in

  map_ts_inv f_andas
    [map_ts_inv1 (f_forall_simpl [(xR_id, GTty tyR)]) cond1;
     map_ts_inv1 (f_forall_simpl [(xR_id, GTty tyR)]) cond2;
     map_ts_inv1 (f_forall_simpl [(xL_id, GTty tyL)]) cond3]

(* Weakest precondition of [x <$ d ~ skip] (for [`Left]; symmetrically for
   [`Right]) for the relation [post]:
     is_lossless d /\ forall v, v \in d => post[x<1> := v] *)
let equiv_rnd_onesided_wp env side ((lv, distr) : lvalue * expr) (post : ts_inv) =
  let ml, mr = post.ml, post.mr in
  let m, mo = sideif side (ml, mr) (mr, ml) in
  let subst_form_lv_side = sideif side subst_form_lv_left subst_form_lv_right in
  let ss_inv_generalize_other =
    sideif side ss_inv_generalize_right ss_inv_generalize_left in
  let ty_distr = proj_distr_ty env (e_ty distr) in

  let x_id = EcIdent.create (symbol_of_lv lv) in
  let x    = {ml; mr; inv=f_local x_id ty_distr} in

  let distr = EcFol.ss_inv_of_expr m distr in
  let distr = ss_inv_generalize_other distr mo in
  let post  = subst_form_lv_side env lv x post in
  let post  = map_ts_inv2 f_imp (map_ts_inv2 f_in_supp x distr) post in
  let post  = map_ts_inv1 (f_forall_simpl [(x_id,GTty ty_distr)]) post in
  map_ts_inv2 f_anda (map_ts_inv1 (f_lossless ty_distr) distr) post

(* -------------------------------------------------------------------- *)
let single_rnd (who : string) (s : stmt) =
  match s.s_node with
  | [{ i_node = Srnd (lv, d) }] -> (lv, d)
  | _ -> failwith (Printf.sprintf "%s: the statement is not a single sampling" who)

(* Pure cores shared by the rules and their checkers. Their side conditions
   (the statements are single samplings — resp. a single sampling and the
   empty statement —, the bijection is well-typed, the precondition is the
   weakest precondition) are part of them, so the checkers re-validate
   them. *)
let equiv_rnd_subgoals (hyps : LDecl.hyps) (es : equivS) (n : equiv_rnd) =
  let env = LDecl.toenv hyps in
  let (_, muL) as rndL = single_rnd "equiv-rnd" es.es_sl in
  let (_, muR) as rndR = single_rnd "equiv-rnd" es.es_sr in
  let ml, mr = fst es.es_ml, fst es.es_mr in
  let n = { ern_f    = ts_inv_rebind n.ern_f    ml mr;
            ern_finv = ts_inv_rebind n.ern_finv ml mr; } in
  let tyL = proj_distr_ty env (e_ty muL) in
  let tyR = proj_distr_ty env (e_ty muR) in
  if not (EcReduction.EqTest.for_type env n.ern_f.inv.f_ty (tfun tyL tyR)) ||
     not (EcReduction.EqTest.for_type env n.ern_finv.inv.f_ty (tfun tyR tyL)) then
    failwith "equiv-rnd: the bijection is ill-typed";
  let wp = equiv_rnd_wp env (rndL, rndR) n (es_po es) in
  if not (EcReduction.ts_inv_alpha_eq hyps wp (es_pr es)) then
    failwith "equiv-rnd: the precondition is not the expected one";
  []

let equiv_rnd_onesided_subgoals
    (hyps : LDecl.hyps) (es : equivS) (n : equiv_rnd_onesided)
=
  let env = LDecl.toenv hyps in
  let s, so = sideif n.eros_side (es.es_sl, es.es_sr) (es.es_sr, es.es_sl) in
  let rnd = single_rnd "equiv-rnd-onesided" s in
  if not (List.is_empty so.s_node) then
    failwith "equiv-rnd-onesided: the other statement is not empty";
  let wp = equiv_rnd_onesided_wp env n.eros_side rnd (es_po es) in
  if not (EcReduction.ts_inv_alpha_eq hyps wp (es_pr es)) then
    failwith "equiv-rnd-onesided: the precondition is not the expected one";
  []

(* -------------------------------------------------------------------- *)
(* Rules (TCB). *)
let t_equiv_rnd (n : equiv_rnd) (tc : tcenv1) =
  let es = tc1_as_equivS tc in
  let sg =
    try  equiv_rnd_subgoals (FApi.tc1_hyps tc) es n
    with Failure msg -> tc_error !!tc "%s" msg in
  FApi.xrule1 tc (REquivRnd n) sg

let t_equiv_rnd_onesided (n : equiv_rnd_onesided) (tc : tcenv1) =
  let es = tc1_as_equivS tc in
  let sg =
    try  equiv_rnd_onesided_subgoals (FApi.tc1_hyps tc) es n
    with Failure msg -> tc_error !!tc "%s" msg in
  FApi.xrule1 tc (REquivRndOneSided n) sg

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | REquivRnd n ->
         Some (EcPlRecheck.checker_of "equiv-rnd" pf_as_equivS
                 (fun hyps es -> equiv_rnd_subgoals hyps es n))
     | REquivRndOneSided n ->
         Some (EcPlRecheck.checker_of "equiv-rnd-onesided" pf_as_equivS
                 (fun hyps es -> equiv_rnd_onesided_subgoals hyps es n))
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* Derived (no proof-node): [seq] before the final samplings, with their
   weakest precondition as intermediate relation, then close the samplings
   with the rules. *)
let t_equiv_rnd_seq bij (tc : tcenv1) =
  let env = FApi.tc1_env tc in
  let es  = tc1_as_equivS tc in
  let ml, mr = fst es.es_ml, fst es.es_mr in
  let rndL, _ = tc1_last_rnd tc es.es_sl in
  let rndR, _ = tc1_last_rnd tc es.es_sr in
  let tyL = proj_distr_ty env (e_ty (snd rndL)) in
  let tyR = proj_distr_ty env (e_ty (snd rndR)) in
  let n =
    match bij with
    | Some (f, finv) -> { ern_f = f tyL tyR; ern_finv = finv tyR tyL; }
    | None ->
      if not (EcReduction.EqTest.for_type env tyL tyR) then
        tc_error !!tc "%s, %s"
          "support are not compatible"
          "an explicit bijection is required";
      { ern_f    = {ml;mr;inv=EcFol.f_identity ~name:"z" tyL};
        ern_finv = {ml;mr;inv=EcFol.f_identity ~name:"z" tyR}; }
  in
  let mid = equiv_rnd_wp env (rndL, rndR) n (es_po es) in
  let at  = gap_before_last_n 1 in
  FApi.t_seqsub
    (EcEquivSeq.t_equiv_seq { esr_at = (at, at); esr_mid = mid })
    [t_id; t_equiv_rnd n]
    tc

let t_equiv_rnd_onesided_seq side (tc : tcenv1) =
  let env = FApi.tc1_env tc in
  let es  = tc1_as_equivS tc in
  let rnd, _ = tc1_last_rnd tc (sideif side es.es_sl es.es_sr) in
  let mid = equiv_rnd_onesided_wp env side rnd (es_po es) in
  let at  = sideif side
    (gap_before_last_n 1, codegap1_end)
    (codegap1_end, gap_before_last_n 1) in
  FApi.t_seqsub
    (EcEquivSeq.t_equiv_seq { esr_at = at; esr_mid = mid })
    [t_id; t_equiv_rnd_onesided { eros_side = side }]
    tc

(* -------------------------------------------------------------------- *)
(* Simplification of the remaining relation (derived): its side conditions
   that [t_solve] proves on their own are turned into separate, closed
   goals, and the relation is weakened accordingly with [conseq].

   TEMPORARY: the consequence rule still comes from the not-yet-migrated
   [EcPhlConseq]. *)
module E = struct exception Abort end

let solve n f tc =
  let tt =
    FApi.t_seqs
      [EcLowGoal.t_intros_n n;
       EcLowGoal.t_solve ~bases:["random"] ~depth:2;
       EcLowGoal.t_fail] in

  let subtc, hd = FApi.newgoal tc f in

  try
    let subtc =
      FApi.t_last
        (fun tc1 ->
          match FApi.t_try_base tt tc1 with
          | `Failure _  -> raise E.Abort
          | `Success tc -> tc)
        subtc
    in (subtc, Some hd)

  with E.Abort -> tc, None

let t_apply_prept pt tc =
  Apply.t_apply_bwd_r (EcProofTerm.pt_of_prept tc pt) tc

(* -------------------------------------------------------------------- *)
let t_equiv_rnd_onesided_last side tc =

  let tc = t_equiv_rnd_onesided_seq side tc in
  let es = tc1_as_equivS (FApi.as_tcenv1 tc) in
  let (c1, c2) = map_ts_inv_destr2 destr_and (es_po es) in
  let newc1 = EcSubst.f_forall_mems_ts_inv es.es_ml es.es_mr c1 in

  let subtc = tc in
  let subtc, hdc1 = solve 2 newc1 subtc in

  match hdc1 with
  | None -> tc
  | Some hd ->
    let po = c2 in
    FApi.t_onalli (function
    | 0 -> fun tc -> EcLowGoal.t_trivial tc
    | 1 ->
      let open EcProofTerm.Prept in
      let m1  = EcIdent.create "_" in
      let m2  = EcIdent.create "_" in
      let h   = EcIdent.create "_" in
      let h1   = EcIdent.create "_" in
      (t_intros_i [m1; m2; h] @!
       (t_split @+
        [ t_apply_prept (hdl hd @ [amem m1; amem m2]);
          t_intros_i [h1] @! t_apply_hyp h]))

    | _ -> EcLowGoal.t_id)
    (FApi.t_first
      (EcPhlConseq.t_equivS_conseq (es_pr es) po)
      subtc)

(* -------------------------------------------------------------------- *)
let t_equiv_rnd_last bij tc =
  let tc = t_equiv_rnd_seq bij tc in
  let es = tc1_as_equivS (FApi.as_tcenv1 tc) in

  let c1, c2, c3 = map_ts_inv_destr3 destr_and3 (es_po es) in
  let (x, xty, _) = destr_forall1 c3.inv in
  let c3 = map_ts_inv1 (fun c3 -> let (_,_,d) = destr_forall1 c3 in d) c3 in
  let (ind, c3) = map_ts_inv_destr2 destr_imp c3 in
  let (c3, c4) = map_ts_inv_destr2 destr_and c3 in
  let newc2 = EcSubst.f_forall_mems_ts_inv es.es_ml es.es_mr c2 in
  let newc3 = EcSubst.f_forall_mems_ts_inv es.es_ml es.es_mr
                (map_ts_inv1 (f_forall [x, xty]) (map_ts_inv2 f_imp ind c3)) in

  let subtc = tc in
  let subtc, hdc2 = solve 4 newc2 subtc in
  let subtc, hdc3 = solve 4 newc3 subtc in

  let po =
    match hdc2, hdc3 with
    | None  , None   -> None
    | Some _, Some _ ->
      Some (map_ts_inv2 f_anda c1 (map_ts_inv1 (f_forall [x, xty]) (map_ts_inv2 f_imp ind c4)))
    | Some _, None   ->
      Some (map_ts_inv2 f_anda c1 (map_ts_inv1 (f_forall [x, xty]) (map_ts_inv2 f_imp ind (map_ts_inv2 f_anda c3 c4))))
    | None  , Some _ ->
      Some (map_ts_inv f_andas [c1; c2; map_ts_inv1 (f_forall [x, xty]) (map_ts_inv2 f_imp ind c4)])
  in

  match po with None -> tc | Some po ->

  let m1  = EcIdent.create "_" in
  let m2  = EcIdent.create "_" in
  let h   = EcIdent.create "_" in
  let h1  = EcIdent.create "_" in
  let h2  = EcIdent.create "_" in
  let x   = EcIdent.create "_" in
  let hin = EcIdent.create "_" in

  FApi.t_onalli (function
    | 0 -> fun tc -> EcLowGoal.t_trivial tc
    | 1 ->
      let open EcProofTerm.Prept in

      let t_c2 =
        let pt =
          match hdc2 with
          | None -> hyp h2
          | Some hd -> hdl hd @ [amem m1; amem m2] in
        t_apply_prept pt in

      let t_c3_c4 =
        match hdc3 with
        | None -> t_apply_prept (hyp h)
        | Some hd ->
          let fx = f_local x (gty_as_ty xty) in
          t_intros_i [x; hin] @! t_split
          @+ [ t_apply_prept (hdl hd @ [amem m1; amem m2; aform fx; ahyp hin]);
               t_intros_n 1 @!
                t_apply_prept ((hyp h) @ [aform fx; ahyp hin])]
      in

      let t_case_c2 =
        match hdc2 with
        | None -> t_elim_and @! t_intros_i [h2; h]
        | Some _ -> t_intros_i [h] in

      t_intros_i [m1; m2] @! t_elim_and @! t_intros_i [h1] @! t_case_c2 @! t_split @+
        [ t_apply_prept (hyp h1);
          t_intros_n 1 @! t_split @+
            [ t_c2;
              t_intros_n 1 @! t_c3_c4
            ]
         ]

    | _ -> EcLowGoal.t_id)

    (FApi.t_first
      (EcPhlConseq.t_equivS_conseq (es_pr es) po)
      subtc)

(* -------------------------------------------------------------------- *)
(* The surface two-sided / one-sided [rnd], optionally preceded by [rndsem]
   on both sides (derived, no proof-node). *)
let t_equiv_rnd_full ?pos side bij_info tc =
  match side, pos, bij_info with
  | Some side, None, (None, None) ->
    t_equiv_rnd_onesided_last side tc
  | Some _side, None, _ ->
    tc_error !!tc "one-sided rnd takes no arguments"
  | None, _, _ -> begin
      let pos =
        match pos with
        | None -> None
        | Some (Single i) -> Some (i, i)
        | Some (Double (il, ir)) -> Some (il, ir) in

      let tc =
        match pos with
        | None ->
           t_id tc
        | Some ((bl, il), (br, ir)) ->
           let open EcEquivRndSem in
           FApi.t_seq
             (t_equiv_rndsem { ersr_side = `Left ; ersr_at = il; ersr_reduce = bl })
             (t_equiv_rndsem { ersr_side = `Right; ersr_at = ir; ersr_reduce = br })
             tc in

      let bij =
        match bij_info with
        | Some f, Some finv ->  Some (f, finv)
        | Some bij, None | None, Some bij -> Some (bij, bij)
        | None, None -> None
      in
      FApi.t_first (t_equiv_rnd_last bij) tc
    end

  | _ ->
    tc_error !!tc "two-sided rnd requires a bijection"

(* -------------------------------------------------------------------- *)
(* Elaboration: the goal is known to be an [equivS]. The bijection(s) are
   typed in the goal's memories once the types of the sampled values are
   known; the positions of [rndsem] (if any) in the memory of their side —
   a single position without side in the bare environment (behaviour
   preserved). *)
let process_equiv_rnd
    (side : oside) (pos : psemrndpos option) (info : rnd_tac_info_f) tc
=
  let process_form f ty1 ty2 =
    TTC.tc1_process_prhl_form tc (tfun ty1 ty2) f in

  let bij_info =
    match info with
    | PNoRndParams -> None, None
    | PSingleRndParam f -> Some (process_form f), None
    | PTwoRndParams (f, finv) -> Some (process_form f), Some (process_form finv)
    | _ -> tc_error !!tc "invalid arguments"
  in

  let pos = pos |> Option.map (function
    | Single (b, p) ->
        let p =
          if Option.is_some side then
            EcLowPhlGoal.tc1_process_codegap1 tc (side, p)
          else EcTyping.trans_codegap1 (FApi.tc1_env tc) p
        in Single (b, p)
    | Double ((b1, p1), (b2, p2)) ->
        let p1 = EcLowPhlGoal.tc1_process_codegap1 tc (Some `Left , p1) in
        let p2 = EcLowPhlGoal.tc1_process_codegap1 tc (Some `Right, p2) in
        Double ((b1, p1), (b2, p2))
  )
  in

  t_equiv_rnd_full side ?pos bij_info tc
