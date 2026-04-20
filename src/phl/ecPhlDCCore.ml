(* -------------------------------------------------------------------- *)
open EcUtils
open EcAst
open EcFol
open EcCoreFol
open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* Two-sided rules for the delayed-coupling logic (paper §4.1).         *)

(* -------------------------------------------------------------------- *)
(* Skip rule (paper).
     Premise:    forall m1 m2, phi m1 m2 implies psi m1 m2
     Conclusion: dcoupl phi [R1xR2] eps eps psi [R1xR2]                  *)
let t_dc_skip_r tc =
  let es = tc1_as_dcEquivS tc in
  if not (List.is_empty es.dces_cl.s_node) then
    tc_error !!tc ~who:"dc skip" "left body is not empty";
  if not (List.is_empty es.dces_cr.s_node) then
    tc_error !!tc ~who:"dc skip" "right body is not empty";
  if not (s_equal es.dces_sl es.dces_rl) then
    tc_error !!tc ~who:"dc skip"
      "left continuation S1 must equal the left delay context R1";
  if not (s_equal es.dces_sr es.dces_rr) then
    tc_error !!tc ~who:"dc skip"
      "right continuation S2 must equal the right delay context R2";
  let concl = map_ts_inv2 f_imp (dces_pr es) (dces_po es) in
  let concl =
    EcSubst.f_forall_mems_ts_inv es.dces_ml es.dces_mr concl
  in
  FApi.xmutate1 tc `DCSkip [concl]

let t_dc_skip = FApi.t_low0 "dc-skip" t_dc_skip_r

(* -------------------------------------------------------------------- *)
(* Helpers for body splitting.                                          *)
let split_at ~who tc n s =
  let nodes = s.EcAst.s_node in
  if List.length nodes < n then
    tc_error !!tc ~who
      "cannot split at position %d (statement has only %d instructions)"
      n (List.length nodes);
  let pre, rest = List.takedrop n nodes in
  (EcAst.stmt pre, EcAst.stmt rest)

let s_cat a b = EcAst.stmt (a.EcAst.s_node @ b.EcAst.s_node)

(* -------------------------------------------------------------------- *)
(* Seq rule (paper).
     Premise 1: dcoupl phi [R1xR2] C1 C2 theta [T1xT2]
     Premise 2: dcoupl theta [T1xT2] D1 D2 psi [S1xS2]
     Conclusion: dcoupl phi [R1xR2] (C1;D1) (C2;D2) psi [S1xS2]

   User splits each body at positions [nl, nr], supplies intermediate
   predicate [theta]. Optional [ts] = (T_l, T_r); if omitted, defaults
   to R_i; C_i.                                                        *)
let t_dc_seq_r ~nl ~nr ?ts theta tc =
  let es = tc1_as_dcEquivS tc in
  let (cl, dl) = split_at ~who:"dc seq" tc nl es.dces_cl in
  let (cr, dr) = split_at ~who:"dc seq" tc nr es.dces_cr in
  let ml = fst es.dces_ml in
  let mr = fst es.dces_mr in
  let theta_ts : ts_inv = { ml; mr; inv = theta } in
  let (tl, tr) =
    match ts with
    | None -> (s_cat es.dces_rl cl, s_cat es.dces_rr cr)
    | Some (tl, tr) -> (tl, tr)
  in
  let sub_left =
    f_dcEquivS (snd es.dces_ml) (snd es.dces_mr)
      (dces_pr es)
      es.dces_rl es.dces_rr cl cr
      theta_ts tl tr
  in
  let sub_right =
    f_dcEquivS (snd es.dces_ml) (snd es.dces_mr)
      theta_ts
      tl tr dl dr
      (dces_po es) es.dces_sl es.dces_sr
  in
  FApi.xmutate1 tc `DCSeq [sub_left; sub_right]

let t_dc_seq ~nl ~nr ?ts theta =
  FApi.t_low0 "dc-seq" (t_dc_seq_r ~nl ~nr ?ts theta)

(* -------------------------------------------------------------------- *)
(* WP: weakest-precondition for a suffix of each body (assignments,
   random samplings, conditionals over pure vars). Does not touch R or
   S contexts, only transforms the post and body. Sound because
   dcoupl's post ranges over witness memories and WP is semantic.      *)
let t_dc_wp_r ?(uselet=true)
    (ij : (EcMatching.Position.codegap1 * EcMatching.Position.codegap1) option)
    tc =
  let hyps = FApi.tc1_hyps tc in
  let env = EcEnv.LDecl.toenv hyps in
  let es = tc1_as_dcEquivS tc in
  let ml, mr = fst es.dces_ml, fst es.dces_mr in
  let i = Option.map fst ij and j = Option.map snd ij in
  let (s_hdl, s_wpl) = o_split env i es.dces_cl in
  let (s_hdr, s_wpr) = o_split env j es.dces_cr in
  let s_wpl = EcAst.stmt s_wpl in
  let s_wpr = EcAst.stmt s_wpr in
  let post = dces_po es in
  let (s_wpl, post) =
    EcPhlWp.wp ~mc:(ml, mr) ~uselet hyps es.dces_ml s_wpl
      (EcAst.POE.empty post.inv)
  in
  let (s_wpr, post) =
    EcPhlWp.wp ~mc:(ml, mr) ~uselet hyps es.dces_mr s_wpr
      (EcAst.POE.empty post)
  in
  if EcUtils.is_some i && not (List.is_empty s_wpl) then
    tc_error !!tc "wp left remaining %d instruction(s)"
      (List.length s_wpl);
  if EcUtils.is_some j && not (List.is_empty s_wpr) then
    tc_error !!tc "wp right remaining %d instruction(s)"
      (List.length s_wpr);
  let cl = EcAst.stmt (s_hdl @ s_wpl) in
  let cr = EcAst.stmt (s_hdr @ s_wpr) in
  let concl =
    f_dcEquivS (snd es.dces_ml) (snd es.dces_mr)
      (dces_pr es)
      es.dces_rl es.dces_rr cl cr
      { ml; mr; inv = post }
      es.dces_sl es.dces_sr
  in
  FApi.xmutate1 tc `DCWp [concl]

let t_dc_wp ?uselet ij =
  FApi.t_low0 "dc-wp" (t_dc_wp_r ?uselet ij)

(* -------------------------------------------------------------------- *)
(* Helpers: coerce a program-expression test [e] into a ts_inv
   formula that references the given memory and is generalized to the
   other side.                                                          *)
let ts_of_test_left ~ml ~mr (e : EcTypes.expr) : EcAst.ts_inv =
  let ssi = EcCoreFol.ss_inv_of_expr ml e in
  EcAst.ss_inv_generalize_right ssi mr

let ts_of_test_right ~ml ~mr (e : EcTypes.expr) : EcAst.ts_inv =
  let ssi = EcCoreFol.ss_inv_of_expr mr e in
  EcAst.ss_inv_generalize_left ssi ml

(* -------------------------------------------------------------------- *)
(* If rule (paper, two-sided).
     Premise 1: dcoupl (phi /\ e1) [R1xR2] C1 C2 psi [S1xS2]
     Premise 2: dcoupl (phi /\ not e1) [R1xR2] C1' C2' psi [S1xS2]
     Premise 3: forall m1 m2, phi m1 m2 implies sem(e1)m1 = sem(e2)m2
     Side conditions: Write(R_i) disjoint from Fv(e_i)
     Conclusion:
       dcoupl phi [R1xR2]
         (if e1 then C1 else C1') (if e2 then C2 else C2')
         psi [S1xS2]                                                     *)
let t_dc_if_r tc =
  let es = tc1_as_dcEquivS tc in
  let env = FApi.tc1_env tc in
  let ml = fst es.dces_ml in
  let mr = fst es.dces_mr in

  (* Body must be a single if on each side. *)
  (match es.dces_cl.EcAst.s_node with
   | [_] -> () | _ -> tc_error !!tc ~who:"dc if"
       "left body must be a single if instruction");
  (match es.dces_cr.EcAst.s_node with
   | [_] -> () | _ -> tc_error !!tc ~who:"dc if"
       "right body must be a single if instruction");
  let (el, sl_t, sl_e) =
    EcCoreModules.destr_if (List.hd es.dces_cl.EcAst.s_node) in
  let (er, sr_t, sr_e) =
    EcCoreModules.destr_if (List.hd es.dces_cr.EcAst.s_node) in

  (* Write side conditions: Write(R_i) disjoint from Fv(e_i). *)
  let fv_el_form = (EcCoreFol.ss_inv_of_expr ml el).inv in
  let fv_er_form = (EcCoreFol.ss_inv_of_expr mr er).inv in
  let fv_el = EcPV.PV.fv env ml fv_el_form in
  let fv_er = EcPV.PV.fv env mr fv_er_form in
  let w_rl = EcPV.s_write env es.dces_rl in
  let w_rr = EcPV.s_write env es.dces_rr in
  if not (EcPV.PV.indep env w_rl fv_el) then
    tc_error !!tc ~who:"dc if"
      "Write(R1) and Fv(e1) are not disjoint";
  if not (EcPV.PV.indep env w_rr fv_er) then
    tc_error !!tc ~who:"dc if"
      "Write(R2) and Fv(e2) are not disjoint";

  (* Test equivalence subgoal. *)
  let el_ts = ts_of_test_left ~ml ~mr el in
  let er_ts = ts_of_test_right ~ml ~mr er in
  let test_eq = map_ts_inv2 f_eq el_ts er_ts in
  let test_impl = map_ts_inv2 f_imp (dces_pr es) test_eq in
  let test_subgoal =
    EcSubst.f_forall_mems_ts_inv es.dces_ml es.dces_mr test_impl
  in

  (* Branch subgoals. *)
  let pre_then = map_ts_inv2 f_and_simpl (dces_pr es) el_ts in
  let pre_else =
    map_ts_inv2 f_and_simpl
      (dces_pr es) (map_ts_inv1 f_not_simpl el_ts)
  in
  let then_goal =
    f_dcEquivS (snd es.dces_ml) (snd es.dces_mr)
      pre_then
      es.dces_rl es.dces_rr sl_t sr_t
      (dces_po es) es.dces_sl es.dces_sr
  in
  let else_goal =
    f_dcEquivS (snd es.dces_ml) (snd es.dces_mr)
      pre_else
      es.dces_rl es.dces_rr sl_e sr_e
      (dces_po es) es.dces_sl es.dces_sr
  in
  FApi.xmutate1 tc `DCIf [test_subgoal; then_goal; else_goal]

let t_dc_if = FApi.t_low0 "dc-if" t_dc_if_r

(* -------------------------------------------------------------------- *)
(* While rule (paper, two-sided).
     Premise 1: dcoupl (phi /\ e1) [R1xR2] C1 C2 phi [R1xR2]
     Premise 2: forall m1 m2, phi m1 m2 implies sem(e1)m1 = sem(e2)m2
     Side conditions: Write(R_i) disjoint from Fv(e_i)
     Conclusion:
       dcoupl phi [R1xR2]
         (while e1 C1) (while e2 C2)
         (phi /\ not e1) [R1xR2]
   Both the post-continuation S_i and the body-loop's post-R equal R_i.
   The caller must pre-arrange this shape (use Conseq if needed).       *)
let t_dc_while_r tc =
  let es = tc1_as_dcEquivS tc in
  let env = FApi.tc1_env tc in
  let ml = fst es.dces_ml in
  let mr = fst es.dces_mr in

  (* Body is a single while on each side. *)
  (match es.dces_cl.EcAst.s_node with
   | [_] -> () | _ -> tc_error !!tc ~who:"dc while"
       "left body must be a single while instruction");
  (match es.dces_cr.EcAst.s_node with
   | [_] -> () | _ -> tc_error !!tc ~who:"dc while"
       "right body must be a single while instruction");
  let (el, body_l) =
    EcCoreModules.destr_while (List.hd es.dces_cl.EcAst.s_node) in
  let (er, body_r) =
    EcCoreModules.destr_while (List.hd es.dces_cr.EcAst.s_node) in

  (* Continuations must match R (the rule's conclusion assumes S = R). *)
  if not (EcAst.s_equal es.dces_sl es.dces_rl) then
    tc_error !!tc ~who:"dc while"
      "left continuation S1 must equal R1";
  if not (EcAst.s_equal es.dces_sr es.dces_rr) then
    tc_error !!tc ~who:"dc while"
      "right continuation S2 must equal R2";

  (* Write side conditions. *)
  let fv_el_form = (EcCoreFol.ss_inv_of_expr ml el).inv in
  let fv_er_form = (EcCoreFol.ss_inv_of_expr mr er).inv in
  let fv_el = EcPV.PV.fv env ml fv_el_form in
  let fv_er = EcPV.PV.fv env mr fv_er_form in
  let w_rl = EcPV.s_write env es.dces_rl in
  let w_rr = EcPV.s_write env es.dces_rr in
  if not (EcPV.PV.indep env w_rl fv_el) then
    tc_error !!tc ~who:"dc while"
      "Write(R1) and Fv(e1) are not disjoint";
  if not (EcPV.PV.indep env w_rr fv_er) then
    tc_error !!tc ~who:"dc while"
      "Write(R2) and Fv(e2) are not disjoint";

  (* The post must be phi /\ not e1 where phi is the pre. *)
  let el_ts = ts_of_test_left ~ml ~mr el in
  let er_ts = ts_of_test_right ~ml ~mr er in
  let phi = dces_pr es in
  let expected_post =
    map_ts_inv2 f_and_simpl phi (map_ts_inv1 f_not_simpl el_ts)
  in
  if not (f_equal (dces_po es).inv expected_post.inv) then
    tc_error !!tc ~who:"dc while"
      "post-condition must be (pre /\\ not e1) \
       (use [dcoupl conseq] to align)";

  (* Subgoal 1: test equivalence. *)
  let test_eq = map_ts_inv2 f_eq el_ts er_ts in
  let test_impl = map_ts_inv2 f_imp phi test_eq in
  let test_subgoal =
    EcSubst.f_forall_mems_ts_inv es.dces_ml es.dces_mr test_impl
  in

  (* Subgoal 2: body preserves invariant. *)
  let pre_body = map_ts_inv2 f_and_simpl phi el_ts in
  let body_goal =
    f_dcEquivS (snd es.dces_ml) (snd es.dces_mr)
      pre_body
      es.dces_rl es.dces_rr body_l body_r
      phi es.dces_rl es.dces_rr
  in
  FApi.xmutate1 tc `DCWhile [test_subgoal; body_goal]

let t_dc_while = FApi.t_low0 "dc-while" t_dc_while_r

(* -------------------------------------------------------------------- *)
(* Rnd (Sample) rule (paper, two-sided).
     User supplies a bijection (f, f_inv) as type-indexed builders that
     produce a ts_inv at the appropriate function types.
     Side conditions: Write(R_i) disjoint from {x_i} ∪ Fv(d_i),
                      x_i not in Read(R_i).
     Post-substitution: post[v, f(v)/x1, x2] is generated.            *)

type dc_bij_builder = EcTypes.ty -> EcTypes.ty -> ts_inv

let t_dc_rnd_r
    (bij : (dc_bij_builder * dc_bij_builder) option)
    tc =
  let env = FApi.tc1_env tc in
  let es = tc1_as_dcEquivS tc in
  let ml = fst es.dces_ml in
  let mr = fst es.dces_mr in

  (* Body must be a single [x <$ d] instruction on each side. *)
  (match es.dces_cl.EcAst.s_node with
   | [_] -> () | _ -> tc_error !!tc ~who:"dc rnd"
       "left body must be a single random assignment");
  (match es.dces_cr.EcAst.s_node with
   | [_] -> () | _ -> tc_error !!tc ~who:"dc rnd"
       "right body must be a single random assignment");

  let (lvL, muL) =
    match (List.hd es.dces_cl.EcAst.s_node).EcAst.i_node with
    | Srnd (lv, d) -> (lv, d)
    | _ -> tc_error !!tc ~who:"dc rnd"
             "left body is not a random assignment"
  in
  let (lvR, muR) =
    match (List.hd es.dces_cr.EcAst.s_node).EcAst.i_node with
    | Srnd (lv, d) -> (lv, d)
    | _ -> tc_error !!tc ~who:"dc rnd"
             "right body is not a random assignment"
  in

  (* Continuations must match R. *)
  if not (EcAst.s_equal es.dces_sl es.dces_rl) then
    tc_error !!tc ~who:"dc rnd"
      "left continuation S1 must equal R1";
  if not (EcAst.s_equal es.dces_sr es.dces_rr) then
    tc_error !!tc ~who:"dc rnd"
      "right continuation S2 must equal R2";

  (* Types. *)
  let tyL = EcFol.proj_distr_ty env (EcTypes.e_ty muL) in
  let tyR = EcFol.proj_distr_ty env (EcTypes.e_ty muR) in

  (* Side conditions: Write(R_i) disjoint from {x_i} ∪ Fv(d_i). *)
  let fv_of_expr m e = EcPV.PV.fv env m (EcCoreFol.ss_inv_of_expr m e).inv in
  let fv_muL = fv_of_expr ml muL in
  let fv_muR = fv_of_expr mr muR in
  let pv_of_lv env m lv =
    match lv with
    | EcAst.LvVar (pv, ty) -> EcPV.PV.add env pv ty EcPV.PV.empty
    | EcAst.LvTuple pvs ->
        List.fold_left
          (fun s (pv, ty) -> EcPV.PV.add env pv ty s)
          EcPV.PV.empty pvs
    |> fun _ -> ignore m;
        List.fold_left
          (fun s (pv, ty) -> EcPV.PV.add env pv ty s)
          EcPV.PV.empty pvs
  in
  let _ = pv_of_lv in
  let lv_fv lv =
    match lv with
    | EcAst.LvVar (pv, ty) -> EcPV.PV.add env pv ty EcPV.PV.empty
    | EcAst.LvTuple pvs ->
        List.fold_left
          (fun s (pv, ty) -> EcPV.PV.add env pv ty s)
          EcPV.PV.empty pvs
  in
  let x_plus_fv_l = EcPV.PV.union (lv_fv lvL) fv_muL in
  let x_plus_fv_r = EcPV.PV.union (lv_fv lvR) fv_muR in
  let w_rl = EcPV.s_write env es.dces_rl in
  let w_rr = EcPV.s_write env es.dces_rr in
  if not (EcPV.PV.indep env w_rl x_plus_fv_l) then
    tc_error !!tc ~who:"dc rnd"
      "Write(R1) and {x1} ∪ Fv(d1) are not disjoint";
  if not (EcPV.PV.indep env w_rr x_plus_fv_r) then
    tc_error !!tc ~who:"dc rnd"
      "Write(R2) and {x2} ∪ Fv(d2) are not disjoint";
  if not (EcPV.PV.indep env (EcPV.s_read env es.dces_rl) (lv_fv lvL)) then
    tc_error !!tc ~who:"dc rnd"
      "x1 occurs in Read(R1)";
  if not (EcPV.PV.indep env (EcPV.s_read env es.dces_rr) (lv_fv lvR)) then
    tc_error !!tc ~who:"dc rnd"
      "x2 occurs in Read(R2)";

  (* Bijection builders. *)
  let tf, tfinv =
    match bij with
    | Some (f, finv) -> (f tyL tyR, finv tyR tyL)
    | None ->
        if not (EcReduction.EqTest.for_type env tyL tyR) then
          tc_error !!tc ~who:"dc rnd"
            "distribution types differ: an explicit bijection is required";
        ({ml; mr; inv = EcFol.f_identity ~name:"z" tyL},
         {ml; mr; inv = EcFol.f_identity ~name:"z" tyR})
  in

  (* Local bound variables over the distribution carriers. *)
  let xL_id =
    EcIdent.create (EcCoreModules.symbol_of_lv lvL ^ "L") in
  let xR_id =
    EcIdent.create (EcCoreModules.symbol_of_lv lvR ^ "R") in
  let xL = { ml; mr; inv = f_local xL_id tyL } in
  let xR = { ml; mr; inv = f_local xR_id tyR } in

  let f_app_simpl' ty f t = f_app_simpl f [t] ty in
  let apply_f    t = map_ts_inv2 (f_app_simpl' tyR) tf    t in
  let apply_finv t = map_ts_inv2 (f_app_simpl' tyL) tfinv t in

  let muL_ts = ss_inv_generalize_right (EcCoreFol.ss_inv_of_expr ml muL) mr in
  let muR_ts = ss_inv_generalize_left  (EcCoreFol.ss_inv_of_expr mr muR) ml in

  (* post[v, f(v) / lvL, lvR]  *)
  let post = EcLowPhlGoal.subst_form_lv_left env lvL xL (dces_po es) in
  let post = EcLowPhlGoal.subst_form_lv_right env lvR (apply_f xL) post in

  let cond_fbij     = map_ts_inv2 f_eq xL (apply_finv (apply_f xL)) in
  let cond_fbij_inv = map_ts_inv2 f_eq xR (apply_f (apply_finv xR)) in

  let cond1 =
    map_ts_inv2 f_imp
      (map_ts_inv2 f_in_supp xR muR_ts)
      cond_fbij_inv
  in
  let cond2 =
    map_ts_inv2 f_imp
      (map_ts_inv2 f_in_supp xR muR_ts)
      (map_ts_inv2 f_eq
         (map_ts_inv2 f_mu_x muR_ts xR)
         (map_ts_inv2 f_mu_x muL_ts (apply_finv xR)))
  in
  let cond3 =
    let body =
      map_ts_inv f_andas
        [map_ts_inv2 f_in_supp (apply_f xL) muR_ts; cond_fbij; post]
    in
    map_ts_inv2 f_imp (map_ts_inv2 f_in_supp xL muL_ts) body
  in

  let required_pre =
    map_ts_inv f_andas
      [ map_ts_inv1 (f_forall_simpl [(xR_id, GTty tyR)]) cond1
      ; map_ts_inv1 (f_forall_simpl [(xR_id, GTty tyR)]) cond2
      ; map_ts_inv1 (f_forall_simpl [(xL_id, GTty tyL)]) cond3 ]
  in

  (* Axiomatic closure + Conseq: generate a single subgoal saying the
     user's pre implies the rule's required pre.                       *)
  let impl = map_ts_inv2 f_imp (dces_pr es) required_pre in
  let subgoal =
    EcSubst.f_forall_mems_ts_inv es.dces_ml es.dces_mr impl in
  FApi.xmutate1 tc `DCRnd [subgoal]

let t_dc_rnd bij = FApi.t_low0 "dc-rnd" (t_dc_rnd_r bij)

(* -------------------------------------------------------------------- *)
(* Symmetry (swap left <-> right).

   Given dcoupl phi [R1xR2] C1 C2 psi [S1xS2], produce the mirrored
   judgment dcoupl phi' [R2xR1] C2 C1 psi' [S2xS1] where phi'/psi'
   are phi/psi with memory identifiers swapped. Useful on its own
   and as a building block for right-side one-sided rules.             *)
let t_dc_sym_r tc =
  let es = tc1_as_dcEquivS tc in
  let (ml, mtl) = es.dces_ml in
  let (mr, mtr) = es.dces_mr in
  let pr =
    { ml; mr; inv = (EcSubst.ts_inv_rebind (dces_pr es) mr ml).inv }
  in
  let po =
    { ml; mr; inv = (EcSubst.ts_inv_rebind (dces_po es) mr ml).inv }
  in
  let concl =
    f_dcEquivS mtr mtl pr
      es.dces_rr es.dces_rl es.dces_cr es.dces_cl
      po es.dces_sr es.dces_sl
  in
  FApi.xmutate1 tc `DCSym [concl]

let t_dc_sym = FApi.t_low0 "dc-sym" t_dc_sym_r

(* -------------------------------------------------------------------- *)
(* One-sided If (paper §4.2, If_L / If_R).
     Side condition: Write(R_side) disjoint from Fv(e_side).
     Subgoals: then-branch and else-branch (no test equivalence). *)
let t_dc_if_side_r ~side tc =
  let es = tc1_as_dcEquivS tc in
  let env = FApi.tc1_env tc in
  let ml = fst es.dces_ml in
  let mr = fst es.dces_mr in

  let (chosen_body, other_body, chosen_m, chosen_R) =
    match side with
    | `Left ->
        (es.dces_cl, es.dces_cr, ml, es.dces_rl)
    | `Right ->
        (es.dces_cr, es.dces_cl, mr, es.dces_rr)
  in
  let _ = other_body in

  (match chosen_body.EcAst.s_node with
   | [_] -> () | _ ->
     tc_error !!tc ~who:"dc if"
       "chosen-side body must be a single if instruction");
  let (e, s_then, s_else) =
    EcCoreModules.destr_if (List.hd chosen_body.EcAst.s_node) in

  (* Side condition: Write(R_side) disjoint from Fv(e). *)
  let fv_e = EcPV.PV.fv env chosen_m
    (EcCoreFol.ss_inv_of_expr chosen_m e).inv in
  let w_r = EcPV.s_write env chosen_R in
  if not (EcPV.PV.indep env w_r fv_e) then
    tc_error !!tc ~who:"dc if"
      "Write(R_side) and Fv(e_side) are not disjoint";

  (* Relational test formula. *)
  let e_ts =
    match side with
    | `Left  -> ts_of_test_left  ~ml ~mr e
    | `Right -> ts_of_test_right ~ml ~mr e
  in
  let pre_then = map_ts_inv2 f_and_simpl (dces_pr es) e_ts in
  let pre_else =
    map_ts_inv2 f_and_simpl
      (dces_pr es) (map_ts_inv1 f_not_simpl e_ts)
  in
  let build (new_cl, new_cr) pre =
    f_dcEquivS (snd es.dces_ml) (snd es.dces_mr)
      pre
      es.dces_rl es.dces_rr new_cl new_cr
      (dces_po es) es.dces_sl es.dces_sr
  in
  let (then_l, then_r), (else_l, else_r) =
    match side with
    | `Left  -> ((s_then, es.dces_cr), (s_else, es.dces_cr))
    | `Right -> ((es.dces_cl, s_then), (es.dces_cl, s_else))
  in
  FApi.xmutate1 tc `DCIfSide
    [ build (then_l, then_r) pre_then
    ; build (else_l, else_r) pre_else ]

let t_dc_if_side ~side = FApi.t_low0 "dc-if-side" (t_dc_if_side_r ~side)

(* -------------------------------------------------------------------- *)
(* One-sided WP: applies WP on the chosen side's body only.             *)
let t_dc_wp_side_r ?(uselet=true) ~side tc =
  let hyps = FApi.tc1_hyps tc in
  let es = tc1_as_dcEquivS tc in
  let ml, mr = fst es.dces_ml, fst es.dces_mr in
  let (mem, body, other_body) =
    match side with
    | `Left  -> (es.dces_ml, es.dces_cl, es.dces_cr)
    | `Right -> (es.dces_mr, es.dces_cr, es.dces_cl)
  in
  let _ = other_body in
  let post = dces_po es in
  let (s_rest, post_new) =
    EcPhlWp.wp ~mc:(ml, mr) ~uselet hyps mem body
      (EcAst.POE.empty post.inv)
  in
  let body_new = EcAst.stmt s_rest in
  let (cl, cr) =
    match side with
    | `Left  -> (body_new, es.dces_cr)
    | `Right -> (es.dces_cl, body_new)
  in
  let concl =
    f_dcEquivS (snd es.dces_ml) (snd es.dces_mr)
      (dces_pr es)
      es.dces_rl es.dces_rr cl cr
      { ml; mr; inv = post_new }
      es.dces_sl es.dces_sr
  in
  FApi.xmutate1 tc `DCWpSide [concl]

let t_dc_wp_side ?uselet ~side =
  FApi.t_low0 "dc-wp-side" (t_dc_wp_side_r ?uselet ~side)

(* -------------------------------------------------------------------- *)
(* One-sided Rnd (paper Samp_L / Samp_R).
     Body on the chosen side is a single random assignment; the other
     side body must be empty. S_i = R_i. Precondition becomes
       Lossless(d) ∧ ∀v ∈ Supp(d), phi[v / x].                           *)
let t_dc_rnd_side_r ~side tc =
  let es = tc1_as_dcEquivS tc in
  let env = FApi.tc1_env tc in
  let ml = fst es.dces_ml in
  let mr = fst es.dces_mr in

  let (chosen_body, other_body, chosen_m, chosen_R) =
    match side with
    | `Left  -> (es.dces_cl, es.dces_cr, ml, es.dces_rl)
    | `Right -> (es.dces_cr, es.dces_cl, mr, es.dces_rr)
  in
  if not (List.is_empty other_body.EcAst.s_node) then
    tc_error !!tc ~who:"dc rnd"
      "the other-side body must be empty for one-sided Rnd";
  (match chosen_body.EcAst.s_node with
   | [_] -> () | _ ->
     tc_error !!tc ~who:"dc rnd"
       "chosen-side body must be a single random assignment");
  let (lv, mu) =
    match (List.hd chosen_body.EcAst.s_node).EcAst.i_node with
    | Srnd (lv, d) -> (lv, d)
    | _ -> tc_error !!tc ~who:"dc rnd"
             "chosen-side body is not a random assignment"
  in

  (* S = R on both sides. *)
  if not (EcAst.s_equal es.dces_sl es.dces_rl) then
    tc_error !!tc ~who:"dc rnd"
      "left continuation S1 must equal R1";
  if not (EcAst.s_equal es.dces_sr es.dces_rr) then
    tc_error !!tc ~who:"dc rnd"
      "right continuation S2 must equal R2";

  let ty_d = EcFol.proj_distr_ty env (EcTypes.e_ty mu) in

  (* Side conditions. *)
  let lv_fv =
    match lv with
    | EcAst.LvVar (pv, ty) -> EcPV.PV.add env pv ty EcPV.PV.empty
    | EcAst.LvTuple pvs ->
        List.fold_left
          (fun s (pv, ty) -> EcPV.PV.add env pv ty s)
          EcPV.PV.empty pvs
  in
  let fv_mu =
    EcPV.PV.fv env chosen_m
      (EcCoreFol.ss_inv_of_expr chosen_m mu).inv
  in
  let w_r = EcPV.s_write env chosen_R in
  if not (EcPV.PV.indep env w_r (EcPV.PV.union lv_fv fv_mu)) then
    tc_error !!tc ~who:"dc rnd"
      "Write(R_side) and {x} ∪ Fv(d) are not disjoint";
  if not (EcPV.PV.indep env (EcPV.s_read env chosen_R) lv_fv) then
    tc_error !!tc ~who:"dc rnd"
      "x occurs in Read(R_side)";

  (* Lossless(d) ∧ ∀v ∈ Supp(d), phi[v / x]. *)
  let x_id =
    EcIdent.create (EcCoreModules.symbol_of_lv lv ^
      (match side with `Left -> "L" | `Right -> "R")) in
  let x_f = f_local x_id ty_d in

  let mu_ss = EcCoreFol.ss_inv_of_expr chosen_m mu in
  let mu_ts =
    match side with
    | `Left  -> ss_inv_generalize_right mu_ss mr
    | `Right -> ss_inv_generalize_left  mu_ss ml
  in

  let post_sub =
    match side with
    | `Left ->
        EcLowPhlGoal.subst_form_lv_left env lv
          { ml; mr; inv = x_f } (dces_po es)
    | `Right ->
        EcLowPhlGoal.subst_form_lv_right env lv
          { ml; mr; inv = x_f } (dces_po es)
  in
  let x_ts : EcAst.ts_inv = { ml; mr; inv = x_f } in
  let in_supp =
    map_ts_inv2 f_in_supp x_ts mu_ts
  in
  let lossless = map_ts_inv1 (f_lossless ty_d) mu_ts in
  let body =
    map_ts_inv2 f_imp in_supp post_sub
  in
  let body =
    map_ts_inv1 (f_forall_simpl [(x_id, GTty ty_d)]) body
  in
  let required_pre = map_ts_inv2 f_and_simpl lossless body in

  (* Axiomatic closure + Conseq: single subgoal that the user's pre
     implies the rule's required pre.                                   *)
  let impl = map_ts_inv2 f_imp (dces_pr es) required_pre in
  let subgoal =
    EcSubst.f_forall_mems_ts_inv es.dces_ml es.dces_mr impl in
  FApi.xmutate1 tc `DCRndSide [subgoal]

let t_dc_rnd_side ~side =
  FApi.t_low0 "dc-rnd-side" (t_dc_rnd_side_r ~side)

(* -------------------------------------------------------------------- *)
(* One-sided While (paper §4.2, While_L / While_R).
     Body on chosen side is a single while; other body must be empty;
     S_i = R_i; post = (pre ∧ ¬e). Produces two subgoals:
       1. termination: {pre | eps × eps} while e C ~ eps {⊤ | eps × eps}
       2. body preserves invariant:
          {pre ∧ e | R × R'} C ~ eps {pre | R × R'}
     (S_i = R_i in subgoal 2).
     Side condition: Write(R_side) disjoint from Fv(e_side). *)
let t_dc_while_side_r ~side tc =
  let es = tc1_as_dcEquivS tc in
  let env = FApi.tc1_env tc in
  let ml = fst es.dces_ml in
  let mr = fst es.dces_mr in

  let (chosen_body, other_body, chosen_m, chosen_R) =
    match side with
    | `Left  -> (es.dces_cl, es.dces_cr, ml, es.dces_rl)
    | `Right -> (es.dces_cr, es.dces_cl, mr, es.dces_rr)
  in
  if not (List.is_empty other_body.EcAst.s_node) then
    tc_error !!tc ~who:"dc while"
      "the other-side body must be empty for one-sided While";
  (match chosen_body.EcAst.s_node with
   | [_] -> () | _ ->
     tc_error !!tc ~who:"dc while"
       "chosen-side body must be a single while instruction");
  let (e, while_body) =
    EcCoreModules.destr_while (List.hd chosen_body.EcAst.s_node) in

  (* Continuations = R. *)
  if not (EcAst.s_equal es.dces_sl es.dces_rl) then
    tc_error !!tc ~who:"dc while"
      "left continuation S1 must equal R1";
  if not (EcAst.s_equal es.dces_sr es.dces_rr) then
    tc_error !!tc ~who:"dc while"
      "right continuation S2 must equal R2";

  (* Side condition. *)
  let fv_e = EcPV.PV.fv env chosen_m
    (EcCoreFol.ss_inv_of_expr chosen_m e).inv in
  let w_r = EcPV.s_write env chosen_R in
  if not (EcPV.PV.indep env w_r fv_e) then
    tc_error !!tc ~who:"dc while"
      "Write(R_side) and Fv(e_side) are not disjoint";

  (* post = pre ∧ ¬e on chosen side. *)
  let phi = dces_pr es in
  let e_ts =
    match side with
    | `Left  -> ts_of_test_left  ~ml ~mr e
    | `Right -> ts_of_test_right ~ml ~mr e
  in
  let expected_post =
    map_ts_inv2 f_and_simpl phi (map_ts_inv1 f_not_simpl e_ts)
  in
  if not (f_equal (dces_po es).inv expected_post.inv) then
    tc_error !!tc ~who:"dc while"
      "post-condition must be (pre /\\ not e_side) \
       (use [dcoupl conseq] to align)";

  (* Subgoal 1: termination in empty contexts. *)
  let s_empty = EcAst.stmt [] in
  let while_stmt = EcAst.stmt [List.hd chosen_body.EcAst.s_node] in
  let (while_cl, while_cr) =
    match side with
    | `Left  -> (while_stmt, s_empty)
    | `Right -> (s_empty, while_stmt)
  in
  let top_post : EcAst.ts_inv = { ml; mr; inv = f_true } in
  let term_goal =
    f_dcEquivS (snd es.dces_ml) (snd es.dces_mr)
      phi
      s_empty s_empty while_cl while_cr
      top_post s_empty s_empty
  in

  (* Subgoal 2: body preserves invariant. *)
  let pre_body = map_ts_inv2 f_and_simpl phi e_ts in
  let (body_cl, body_cr) =
    match side with
    | `Left  -> (while_body, s_empty)
    | `Right -> (s_empty, while_body)
  in
  let body_goal =
    f_dcEquivS (snd es.dces_ml) (snd es.dces_mr)
      pre_body
      es.dces_rl es.dces_rr body_cl body_cr
      phi es.dces_rl es.dces_rr
  in
  FApi.xmutate1 tc `DCWhileSide [term_goal; body_goal]

let t_dc_while_side ~side =
  FApi.t_low0 "dc-while-side" (t_dc_while_side_r ~side)

(* -------------------------------------------------------------------- *)
(* Cond_L (paper §4.2, key delay rule).

   Premise:    { phi | R1;x1<$d1  x  R2 }
                 y1 <- e1  ~  c2
               { psi | R1  x  S2 }

   Conclusion: { phi | R1;x1<$d1  x  R2 }
                 y1 <- e1  ~  c2
               { psi | R1;x1<$(d1 | λv. e1[v/x1] = y1)  x  S2 }

   Applied as a backward tactic: given a goal matching the CONCLUSION
   shape (i.e., S1 ends in a random assignment to [x1] whose prefix
   matches R1's prefix), reduce to the PREMISE (drop the conditional
   sample from S1).

   The tactic does not semantically verify that the distribution on
   [x1] in [S1] is [d1 | cond]; it trusts the user and only checks
   structural prerequisites (bodies, prefixes, same sampled variable).
   A stronger version would compare the distributions up to
   conversion.                                                          *)
let split_last ~who tc (s : EcAst.stmt) =
  match List.rev s.EcAst.s_node with
  | [] -> tc_error !!tc ~who "statement is empty"
  | last :: rev_init ->
      (EcAst.stmt (List.rev rev_init), last)

let destr_rnd_i tc (i : EcAst.instr) =
  match i.EcAst.i_node with
  | Srnd (lv, d) -> (lv, d)
  | _ -> tc_error !!tc ~who:"dc cond"
           "expected a random assignment instruction"

let destr_asgn_i tc (i : EcAst.instr) =
  match i.EcAst.i_node with
  | Sasgn (lv, e) -> (lv, e)
  | _ -> tc_error !!tc ~who:"dc cond"
           "expected a (deterministic) assignment instruction"

(* Match [d_cond] as [Distr.dcond d_inner pred_inner]; returns
   [(d_inner, pred_inner)] or raises a tc_error. *)
let destr_dcond tc (d_cond : EcTypes.expr) =
  match EcTypes.destr_app d_cond with
  | (hd, [d_inner; pred_inner]) ->
      (match hd.EcAst.e_node with
       | EcAst.Eop (p, _tys)
         when EcPath.p_equal p EcCoreLib.CI_Distr.p_dcond ->
           (d_inner, pred_inner)
       | _ ->
           tc_error !!tc ~who:"dc cond_l"
             "S-side trailing sample does not have the form [Distr.dcond d p]")
  | _ ->
      tc_error !!tc ~who:"dc cond_l"
        "S-side trailing sample does not have the form [Distr.dcond d p]"

let t_dc_cond_l_r tc =
  let es = tc1_as_dcEquivS tc in
  let hyps = FApi.tc1_hyps tc in
  let env = FApi.tc1_env tc in
  let ml = fst es.dces_ml in

  (* body_l must be a single deterministic assignment y <- e *)
  let asgn_i =
    match es.dces_cl.EcAst.s_node with
    | [i] -> i
    | _ -> tc_error !!tc ~who:"dc cond_l"
             "left body must be a single assignment"
  in
  let (lv_y, e_y) = destr_asgn_i tc asgn_i in

  (* R_l must end in a random assignment x <$ d. *)
  let (r_pre, r_last) = split_last ~who:"dc cond_l" tc es.dces_rl in
  let (lv_x, d_orig)  = destr_rnd_i tc r_last in

  (* S_l must end in a random assignment on the same lvalue. *)
  let (s_pre, s_last) = split_last ~who:"dc cond_l" tc es.dces_sl in
  let (lv_x', d_cond) = destr_rnd_i tc s_last in

  if not (EcAst.lv_equal lv_x lv_x') then
    tc_error !!tc ~who:"dc cond_l"
      "R1 and S1 must end in a random assignment on the same variable";

  (* Prefixes of R_l and S_l must match. *)
  if not (EcAst.s_equal r_pre s_pre) then
    tc_error !!tc ~who:"dc cond_l"
      "R1 and S1 must share a common prefix before the trailing sample";

  (* Semantic check:
     S_l's trailing distribution must be [dcond d_orig (fun v => e_y[v/x] = y)].
     We compare as formulas modulo alpha-equivalence and conversion.         *)
  let (d_inner_e, pred_inner_e) = destr_dcond tc d_cond in

  (* Require lv_x and lv_y to be LvVar (simple variables) for the check. *)
  let (pv_x, ty_x) =
    match lv_x with
    | EcAst.LvVar (pv, ty) -> (pv, ty)
    | _ ->
        tc_error !!tc ~who:"dc cond_l"
          "the trailing sampled lvalue must be a single variable"
  in
  let (pv_y, ty_y) =
    match lv_y with
    | EcAst.LvVar (pv, ty) -> (pv, ty)
    | _ ->
        tc_error !!tc ~who:"dc cond_l"
          "the body's assigned lvalue must be a single variable"
  in

  (* Compare inner distribution with R_l's trailing distribution. *)
  let d_orig_f = (EcCoreFol.ss_inv_of_expr ml d_orig).inv in
  let d_inner_f = (EcCoreFol.ss_inv_of_expr ml d_inner_e).inv in
  if not (EcReduction.is_conv hyps d_orig_f d_inner_f) then
    tc_error !!tc ~who:"dc cond_l"
      "S1's conditional distribution's source does not match R1's distribution";

  (* Build the expected predicate [fun v => e[v/x] = y] as a ss_inv. *)
  let v_id = EcIdent.create "v" in
  let v_ss : EcAst.ss_inv = { m = ml; inv = f_local v_id ty_x } in
  let e_ss = EcCoreFol.ss_inv_of_expr ml e_y in
  let e_sub_ss =
    EcLowPhlGoal.subst_form_lv env (EcAst.LvVar (pv_x, ty_x)) v_ss e_ss
  in
  let y_ss = EcCoreFol.f_pvar pv_y ty_y ml in
  let eq_f = f_eq e_sub_ss.inv y_ss.inv in
  let expected_pred_f = f_lambda [(v_id, GTty ty_x)] eq_f in

  (* Compare with the actual predicate (up to conversion/alpha). *)
  let actual_pred_f = (EcCoreFol.ss_inv_of_expr ml pred_inner_e).inv in
  if not (EcReduction.is_conv hyps expected_pred_f actual_pred_f) then
    tc_error !!tc ~who:"dc cond_l"
      "S1's conditioning predicate does not match [fun v => e[v/x] = y]";

  (* Everything checks: drop the trailing sample from S_l. *)
  let new_sl = s_pre in
  let concl =
    f_dcEquivS (snd es.dces_ml) (snd es.dces_mr)
      (dces_pr es)
      es.dces_rl es.dces_rr es.dces_cl es.dces_cr
      (dces_po es) new_sl es.dces_sr
  in
  FApi.xmutate1 tc `DCCondL [concl]

let t_dc_cond_l = FApi.t_low0 "dc-cond-l" t_dc_cond_l_r

(* -------------------------------------------------------------------- *)
(* Unfold a dcEquivF goal into a dcEquivS goal by inlining the two
   procedures' bodies in [C_l] / [C_r]. Mirrors [t_equivF_fun_def] for
   equiv. The surrounding delay/continuation contexts are unchanged. *)
let t_dc_fun_def_r tc =
  let env = FApi.tc1_env tc in
  let ef = tc1_as_dcEquivF tc in
  let ml, mr = ef.dcef_ml, ef.dcef_mr in
  let fl = EcEnv.NormMp.norm_xfun env ef.dcef_fl in
  let fr = EcEnv.NormMp.norm_xfun env ef.dcef_fr in
  EcPhlFun.check_concrete !!tc env fl;
  EcPhlFun.check_concrete !!tc env fr;
  let (menvl, eqsl, menvr, eqsr, env) =
    EcEnv.Fun.equivS ml mr fl fr env in
  let (fsigl, fdefl) = eqsl in
  let (fsigr, fdefr) = eqsr in
  let fresl =
    EcUtils.odfl { EcAst.m = ml; EcAst.inv = f_tt }
      (Option.map (EcCoreFol.ss_inv_of_expr ml) fdefl.f_ret) in
  let fresr =
    EcUtils.odfl { EcAst.m = mr; EcAst.inv = f_tt }
      (Option.map (EcCoreFol.ss_inv_of_expr mr) fdefr.f_ret) in
  let s = EcPV.PVM.add env EcTypes.pv_res ml fresl.inv EcPV.PVM.empty in
  let s = EcPV.PVM.add env EcTypes.pv_res mr fresr.inv s in
  let post = map_ts_inv1 (EcPV.PVM.subst env s) (dcef_po ef) in
  let s = EcPhlFun.subst_pre env fsigl ml EcPV.PVM.empty in
  let s = EcPhlFun.subst_pre env fsigr mr s in
  let pre = map_ts_inv1 (EcPV.PVM.subst env s) (dcef_pr ef) in
  let concl' =
    f_dcEquivS (snd menvl) (snd menvr) pre
      ef.dcef_rl ef.dcef_rr
      fdefl.f_body fdefr.f_body
      post
      ef.dcef_sl ef.dcef_sr
  in
  FApi.xmutate1 tc `DCFunDef [concl']

let t_dc_fun_def = FApi.t_low0 "dc-fun-def" t_dc_fun_def_r

(* -------------------------------------------------------------------- *)
(* Unroll_L / Unroll_R (paper §4.3).

     Goal: body on chosen side = single [while e do c].
     Transform into: body = [if e then (c; while e do c) else skip].
   This is the "unroll one iteration" rewrite.                          *)
let t_dc_unroll_side_r ~side tc =
  let es = tc1_as_dcEquivS tc in

  let chosen_body =
    match side with
    | `Left  -> es.dces_cl
    | `Right -> es.dces_cr
  in
  (match chosen_body.EcAst.s_node with
   | [_] -> () | _ ->
     tc_error !!tc ~who:"dc unroll"
       "chosen-side body must be a single while instruction");
  let while_i = List.hd chosen_body.EcAst.s_node in
  let (e, c) = EcCoreModules.destr_while while_i in

  (* Build [if e then (c; while e do c) else skip]. *)
  let while_stmt = EcAst.stmt [while_i] in
  let then_stmt = EcAst.stmt (c.EcAst.s_node @ while_stmt.EcAst.s_node) in
  let else_stmt = EcAst.stmt [] in
  let if_instr =
    EcCoreModules.i_if (e, then_stmt, else_stmt) in
  let new_body = EcAst.stmt [if_instr] in

  let (new_cl, new_cr) =
    match side with
    | `Left  -> (new_body, es.dces_cr)
    | `Right -> (es.dces_cl, new_body)
  in
  let concl =
    f_dcEquivS (snd es.dces_ml) (snd es.dces_mr)
      (dces_pr es)
      es.dces_rl es.dces_rr new_cl new_cr
      (dces_po es) es.dces_sl es.dces_sr
  in
  FApi.xmutate1 tc `DCUnrollSide [concl]

let t_dc_unroll_side ~side =
  FApi.t_low0 "dc-unroll-side" (t_dc_unroll_side_r ~side)

(* -------------------------------------------------------------------- *)
(* Split_L / Split_R (paper §4.3).

     Goal: body on chosen side = single [while e do c].
     User supplies an additional predicate [e'].
     Transform into: body = [while e ∧ e' do c; while e do c].          *)
let t_dc_split_side_r ~side (e' : EcTypes.expr) tc =
  let es = tc1_as_dcEquivS tc in

  let chosen_body =
    match side with
    | `Left  -> es.dces_cl
    | `Right -> es.dces_cr
  in
  (match chosen_body.EcAst.s_node with
   | [_] -> () | _ ->
     tc_error !!tc ~who:"dc split"
       "chosen-side body must be a single while instruction");
  let while_i = List.hd chosen_body.EcAst.s_node in
  let (e, c) = EcCoreModules.destr_while while_i in

  (* [e'] must have boolean type. *)
  let env = FApi.tc1_env tc in
  if not (EcReduction.EqTest.for_type env EcTypes.tbool (EcTypes.e_ty e')) then
    tc_error !!tc ~who:"dc split"
      "the supplied split predicate must be of type [bool]";

  (* Build [while e ∧ e' do c; while e do c]. *)
  let e_and =
    EcTypes.e_app
      (EcTypes.e_op EcCoreLib.CI_Bool.p_and [] EcTypes.(toarrow [tbool; tbool] tbool))
      [e; e']
      EcTypes.tbool
  in
  let strict_while = EcCoreModules.i_while (e_and, c) in
  let loose_while  = EcCoreModules.i_while (e, c) in
  let new_body = EcAst.stmt [strict_while; loose_while] in

  let (new_cl, new_cr) =
    match side with
    | `Left  -> (new_body, es.dces_cr)
    | `Right -> (es.dces_cl, new_body)
  in
  let concl =
    f_dcEquivS (snd es.dces_ml) (snd es.dces_mr)
      (dces_pr es)
      es.dces_rl es.dces_rr new_cl new_cr
      (dces_po es) es.dces_sl es.dces_sr
  in
  FApi.xmutate1 tc `DCSplitSide [concl]

let t_dc_split_side ~side e' =
  FApi.t_low0 "dc-split-side" (t_dc_split_side_r ~side e')

(* -------------------------------------------------------------------- *)
(* Cond_L intro direction (paper §4.2 used forward).
     Input:  { phi | R_1; x<$d × R_2 } y<-e ~ c_2 { psi | R_1 × S_2 }
     Output: { phi | R_1; x<$d × R_2 } y<-e ~ c_2
               { psi | R_1; x<$(dcond d (fun v => e[v/x]=y)) × S_2 }    *)
let rec e_subst_pv_expr
    (pv_x : EcAst.prog_var)
    (v : EcTypes.expr)
    (e : EcTypes.expr)
    : EcTypes.expr =
  match e.EcAst.e_node with
  | EcAst.Evar pv when EcAst.pv_equal pv pv_x -> v
  | _ -> EcTypes.e_map (fun ty -> ty) (e_subst_pv_expr pv_x v) e

let t_dc_cond_l_intro_r tc =
  let es = tc1_as_dcEquivS tc in

  (* body_l must be a single deterministic assignment y <- e *)
  let asgn_i =
    match es.dces_cl.EcAst.s_node with
    | [i] -> i
    | _ -> tc_error !!tc ~who:"dc cond intro"
             "left body must be a single assignment"
  in
  let (lv_y, e_y) = destr_asgn_i tc asgn_i in

  (* R_l must end in a random assignment x <$ d. *)
  let (r_pre, r_last) = split_last ~who:"dc cond intro" tc es.dces_rl in
  let (lv_x, d_orig)  = destr_rnd_i tc r_last in

  (* S_l must equal R_l's prefix (R_l minus the trailing sample). *)
  if not (EcAst.s_equal es.dces_sl r_pre) then
    tc_error !!tc ~who:"dc cond intro"
      "S1 must equal R1 without its trailing sample";

  let (pv_x, ty_x) =
    match lv_x with
    | EcAst.LvVar (pv, ty) -> (pv, ty)
    | _ -> tc_error !!tc ~who:"dc cond intro"
             "the trailing sampled lvalue must be a single variable"
  in
  let (pv_y, ty_y) =
    match lv_y with
    | EcAst.LvVar (pv, ty) -> (pv, ty)
    | _ -> tc_error !!tc ~who:"dc cond intro"
             "the body's assigned lvalue must be a single variable"
  in

  (* Build [dcond d (fun v => e[v/x] = y)]. *)
  let v_id = EcIdent.create "v" in
  let v_expr = EcTypes.e_local v_id ty_x in
  let e_sub = e_subst_pv_expr pv_x v_expr e_y in
  let y_expr = EcTypes.e_var pv_y ty_y in
  let eq_expr =
    EcTypes.e_app
      (EcTypes.e_op EcCoreLib.CI_Bool.p_eq [ty_y]
         EcTypes.(toarrow [ty_y; ty_y] tbool))
      [e_sub; y_expr]
      EcTypes.tbool
  in
  let pred_expr = EcTypes.e_lam [(v_id, ty_x)] eq_expr in
  let dcond_op =
    EcTypes.e_op EcCoreLib.CI_Distr.p_dcond [ty_x]
      EcTypes.(toarrow
        [tdistr ty_x; toarrow [ty_x] tbool] (tdistr ty_x))
  in
  let new_d =
    EcTypes.e_app dcond_op [d_orig; pred_expr] (EcTypes.tdistr ty_x) in
  let new_sample = EcCoreModules.i_rnd (lv_x, new_d) in
  let new_sl = EcAst.stmt (es.dces_sl.EcAst.s_node @ [new_sample]) in

  let concl =
    f_dcEquivS (snd es.dces_ml) (snd es.dces_mr)
      (dces_pr es)
      es.dces_rl es.dces_rr es.dces_cl es.dces_cr
      (dces_po es) new_sl es.dces_sr
  in
  FApi.xmutate1 tc `DCCondLIntro [concl]

let t_dc_cond_l_intro = FApi.t_low0 "dc-cond-l-intro" t_dc_cond_l_intro_r

(* Cond_R is obtainable via symmetry, but expose it directly for UX. *)
let t_dc_cond_side ~side tc =
  match side with
  | `Left  -> t_dc_cond_l tc
  | `Right ->
      FApi.t_seqs
        [ t_dc_sym
        ; t_dc_cond_l
        ; t_dc_sym ]
        tc

let t_dc_cond_intro_side ~side tc =
  match side with
  | `Left  -> t_dc_cond_l_intro tc
  | `Right ->
      FApi.t_seqs
        [ t_dc_sym
        ; t_dc_cond_l_intro
        ; t_dc_sym ]
        tc

(* -------------------------------------------------------------------- *)
(* Prod_L (paper §4.3, bidirectional).

     Premise:    { phi | R_1; x_1<$d_1; y_1<$d_1'  x  R_2 } ... { ... }
     Conclusion: { phi | R_1; (x_1, y_1)<$(d_1 `*` d_1')  x  R_2 } ... { ... }
     Side cond (intro only): x_1 not in Fv(d_1').

   Direction [`Split]: R_side ends in a product sample; expand into two
   sequential samples.
   Direction [`Intro]: R_side ends in two consecutive samples; combine
   into a product sample (side condition checked).                     *)
let t_dc_prod_split_r ~side tc =
  let es = tc1_as_dcEquivS tc in
  let chosen_R =
    match side with `Left -> es.dces_rl | `Right -> es.dces_rr in
  let (r_pre, r_last) =
    split_last ~who:"dc prod" tc chosen_R in
  let (lv, d) = destr_rnd_i tc r_last in
  let (pvs, tys) =
    match lv with
    | EcAst.LvTuple pvs ->
        (List.map fst pvs, List.map snd pvs)
    | _ ->
        tc_error !!tc ~who:"dc prod"
          "R-side's trailing sample must be a tuple assignment"
  in
  let () =
    match pvs with
    | [_; _] -> ()
    | _ ->
        tc_error !!tc ~who:"dc prod"
          "R-side's trailing product sample must have exactly 2 components"
  in
  let (pv_x, pv_y) = (List.nth pvs 0, List.nth pvs 1) in
  let (ty_x, ty_y) = (List.nth tys 0, List.nth tys 1) in

  let (d1, d2) =
    match EcTypes.destr_app d with
    | (hd, [d1; d2]) ->
        (match hd.EcAst.e_node with
         | EcAst.Eop (p, _)
           when EcPath.p_equal p EcCoreLib.CI_Distr.p_dprod ->
             (d1, d2)
         | _ ->
             tc_error !!tc ~who:"dc prod"
               "R-side's trailing distribution is not a product \
                [Distr.`*`]")
    | _ ->
        tc_error !!tc ~who:"dc prod"
          "R-side's trailing distribution is not a product \
           [Distr.`*`]"
  in

  let i_x = EcCoreModules.i_rnd (EcAst.LvVar (pv_x, ty_x), d1) in
  let i_y = EcCoreModules.i_rnd (EcAst.LvVar (pv_y, ty_y), d2) in
  let new_R = EcAst.stmt (r_pre.EcAst.s_node @ [i_x; i_y]) in
  let (new_rl, new_rr) =
    match side with
    | `Left  -> (new_R, es.dces_rr)
    | `Right -> (es.dces_rl, new_R)
  in
  let concl =
    f_dcEquivS (snd es.dces_ml) (snd es.dces_mr)
      (dces_pr es)
      new_rl new_rr es.dces_cl es.dces_cr
      (dces_po es) es.dces_sl es.dces_sr
  in
  FApi.xmutate1 tc `DCProdSplit [concl]

let t_dc_prod_split ~side =
  FApi.t_low0 "dc-prod-split" (t_dc_prod_split_r ~side)

(* Intro direction: combines the last two R-samples into a product. *)
let t_dc_prod_intro_r ~side tc =
  let es = tc1_as_dcEquivS tc in
  let env = FApi.tc1_env tc in
  let chosen_R =
    match side with `Left -> es.dces_rl | `Right -> es.dces_rr in
  let chosen_m =
    match side with
    | `Left  -> fst es.dces_ml
    | `Right -> fst es.dces_mr
  in
  (* R_side must have at least two instructions; both must be rnds. *)
  let nodes = chosen_R.EcAst.s_node in
  let n = List.length nodes in
  if n < 2 then
    tc_error !!tc ~who:"dc prod intro"
      "R-side must end in two random assignments";
  let i_n2 = List.nth nodes (n - 2) in
  let i_n1 = List.nth nodes (n - 1) in
  let r_pre = EcAst.stmt (List.take (n - 2) nodes) in
  let (lv_x, d1) = destr_rnd_i tc i_n2 in
  let (lv_y, d2) = destr_rnd_i tc i_n1 in
  let (pv_x, ty_x) =
    match lv_x with
    | EcAst.LvVar (pv, ty) -> (pv, ty)
    | _ ->
        tc_error !!tc ~who:"dc prod intro"
          "the second-to-last R-side sample must be a single-variable assignment"
  in
  let (pv_y, ty_y) =
    match lv_y with
    | EcAst.LvVar (pv, ty) -> (pv, ty)
    | _ ->
        tc_error !!tc ~who:"dc prod intro"
          "the last R-side sample must be a single-variable assignment"
  in

  (* Side condition: x not in Fv(d2). *)
  let fv_d2 = EcPV.PV.fv env chosen_m
    (EcCoreFol.ss_inv_of_expr chosen_m d2).inv in
  let pv_x_set = EcPV.PV.add env pv_x ty_x EcPV.PV.empty in
  if not (EcPV.PV.indep env pv_x_set fv_d2) then
    tc_error !!tc ~who:"dc prod intro"
      "side condition fails: x occurs in Fv(d2)";

  (* Build product distribution. *)
  let prod_ty = EcTypes.ttuple [ty_x; ty_y] in
  let prod_op =
    EcTypes.e_op EcCoreLib.CI_Distr.p_dprod [ty_x; ty_y]
      EcTypes.(toarrow
        [tdistr ty_x; tdistr ty_y] (tdistr prod_ty))
  in
  let d_prod =
    EcTypes.e_app prod_op [d1; d2] (EcTypes.tdistr prod_ty)
  in
  let tuple_lv =
    EcAst.LvTuple [(pv_x, ty_x); (pv_y, ty_y)] in
  let new_sample = EcCoreModules.i_rnd (tuple_lv, d_prod) in
  let new_R = EcAst.stmt (r_pre.EcAst.s_node @ [new_sample]) in
  let (new_rl, new_rr) =
    match side with
    | `Left  -> (new_R, es.dces_rr)
    | `Right -> (es.dces_rl, new_R)
  in
  let concl =
    f_dcEquivS (snd es.dces_ml) (snd es.dces_mr)
      (dces_pr es)
      new_rl new_rr es.dces_cl es.dces_cr
      (dces_po es) es.dces_sl es.dces_sr
  in
  FApi.xmutate1 tc `DCProdIntro [concl]

let t_dc_prod_intro ~side =
  FApi.t_low0 "dc-prod-intro" (t_dc_prod_intro_r ~side)
