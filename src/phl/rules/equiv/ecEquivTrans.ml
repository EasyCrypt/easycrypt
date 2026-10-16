(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcTypes
open EcFol
open EcEnv
open EcPV
open EcMatching
open EcTransMatching
open EcMaps
open EcAst

open EcCoreGoal
open EcLowPhlGoal

module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
(* Parameters of the equiv transitivity rules: the intermediate program and
   the two relations, already typed, nothing to resolve: the same record is
   the rule argument and the node payload. The relations [P1, Q1] are stated
   over (left, intermediate), [P2, Q2] over (intermediate, right); all four
   use the memories of the goal, the intermediate one taking the name of the
   right (resp. left) memory. *)
type equivS_trans = {
  est_mt    : EcMemory.memtype;   (* memory type of the intermediate program *)
  est_stmt  : stmt;               (* intermediate program c2 *)
  est_pre1  : ts_inv;             (* P1, over (left, intermediate) *)
  est_post1 : ts_inv;             (* Q1, over (left, intermediate) *)
  est_pre2  : ts_inv;             (* P2, over (intermediate, right) *)
  est_post2 : ts_inv;             (* Q2, over (intermediate, right) *)
}

type equivF_trans = {
  eft_f     : EcPath.xpath;       (* intermediate procedure f2 *)
  eft_pre1  : ts_inv;             (* P1, over (left, intermediate) *)
  eft_post1 : ts_inv;             (* Q1, over (left, intermediate) *)
  eft_pre2  : ts_inv;             (* P2, over (intermediate, right) *)
  eft_post2 : ts_inv;             (* Q2, over (intermediate, right) *)
}

type EcCoreGoal.rule +=
  | REquivSTrans of equivS_trans
  | REquivFTrans of equivF_trans

(* -------------------------------------------------------------------- *)
(* The composition side conditions, on the goal's pre/post [p] / [q]:
   - cond1: [forall &1 &3, P => exists (fv P1<2>, fv P2<2>), P1 /\ P2], the
     intermediate memory being represented by the program variables and
     globals of P1 and P2 it binds;
   - cond2: [forall &1 &2 &3, Q1 => Q2 => Q].
   [prml, prmr] / [poml, pomr] are the pre / post memories of the goal,
   [pomt] the type of the intermediate post memory. *)
let trans_side_conds
    hyps prml prmr poml pomr (p : ts_inv) (q : ts_inv)
    (p1 : ts_inv) (q1 : ts_inv) pomt (p2 : ts_inv) (q2 : ts_inv)
=
  let env = LDecl.toenv hyps in
  let cond1 =
    let fv1 = PV.fv env p1.mr p1.inv in
    let fv2 = PV.fv env p2.ml p2.inv in
    let fv  = PV.union fv1 fv2 in
    let elts, glob = PV.ntr_elements fv in
    let m = EcIdent.create "&m" in
    let bd, s = generalize_subst env m elts glob in
    let s1 = PVM.of_mpv s p.mr in
    let s2 = PVM.of_mpv s p.ml in
    let concl =
      map_ts_inv2 f_and
        (map_ts_inv1 (PVM.subst env s1) p1)
        (map_ts_inv1 (PVM.subst env s2) p2) in
    EcSubst.f_forall_mems_ts_inv prml prmr
      (map_ts_inv2 f_imp p (map_ts_inv1 (f_exists bd) concl)) in
  let cond2 =
    let m2 = LDecl.fresh_id hyps "&m" in
    let q1 = (EcSubst.ts_inv_rebind_right q1 m2).inv in
    let q2 = (EcSubst.ts_inv_rebind_left q2 m2).inv in
    f_forall_mems [poml; (m2, pomt); pomr] (f_imps [q1; q2] q.inv) in
  (cond1, cond2)

(* Side condition of both rules: the four relations are stated over the
   goal's memories [(ml, mr)]. *)
let check_trans_mems name ml mr (invs : ts_inv list) =
  List.iter (fun (inv : ts_inv) ->
      if not (EcIdent.id_equal inv.ml ml && EcIdent.id_equal inv.mr mr) then
        failwith (name ^ ": relation not stated over the goal's memories"))
    invs

(* -------------------------------------------------------------------- *)
(* Pure cores shared by the rules and their checkers. They need the
   environment: cond1 quantifies over the variables of the intermediate
   memory read by P1 and P2, and the procedure form computes the memories of
   the procedures. *)
let equivS_trans_subgoals (hyps : LDecl.hyps) (es : equivS) (n : equivS_trans) =
  let ml, mr = es.es_ml, es.es_mr in
  check_trans_mems "equivS-trans" (fst ml) (fst mr)
    [n.est_pre1; n.est_post1; n.est_pre2; n.est_post2];
  let cond1, cond2 =
    trans_side_conds hyps ml mr ml mr (es_pr es) (es_po es)
      n.est_pre1 n.est_post1 n.est_mt n.est_pre2 n.est_post2 in
  let cond3 =
    f_equivS (snd ml) n.est_mt n.est_pre1 es.es_sl n.est_stmt n.est_post1 in
  let cond4 =
    f_equivS n.est_mt (snd mr) n.est_pre2 n.est_stmt es.es_sr n.est_post2 in
  [cond1; cond2; cond3; cond4]

let equivF_trans_subgoals (hyps : LDecl.hyps) (ef : equivF) (n : equivF_trans) =
  let env = LDecl.toenv hyps in
  check_trans_mems "equivF-trans" ef.ef_ml ef.ef_mr
    [n.eft_pre1; n.eft_post1; n.eft_pre2; n.eft_post2];
  let (prml, prmr), (poml, pomr) =
    Fun.equivF_memenv ef.ef_ml ef.ef_mr ef.ef_fl ef.ef_fr env in
  let _, (_, pomt) = Fun.hoareF_memenv n.eft_pre1.ml n.eft_f env in
  let cond1, cond2 =
    trans_side_conds hyps prml prmr poml pomr (ef_pr ef) (ef_po ef)
      n.eft_pre1 n.eft_post1 pomt n.eft_pre2 n.eft_post2 in
  let cond3 = f_equivF n.eft_pre1 ef.ef_fl n.eft_f n.eft_post1 in
  let cond4 = f_equivF n.eft_pre2 n.eft_f ef.ef_fr n.eft_post2 in
  [cond1; cond2; cond3; cond4]

(* -------------------------------------------------------------------- *)
(* Rules (TCB). *)
let t_equivS_trans (r : equivS_trans) (tc : tcenv1) =
  let es = tc1_as_equivS tc in
  FApi.xrule1 tc (REquivSTrans r)
    (equivS_trans_subgoals (FApi.tc1_hyps tc) es r)

let t_equivF_trans (r : equivF_trans) (tc : tcenv1) =
  let ef = tc1_as_equivF tc in
  FApi.xrule1 tc (REquivFTrans r)
    (equivF_trans_subgoals (FApi.tc1_hyps tc) ef r)

(* -------------------------------------------------------------------- *)
(* Checkers: rerun the cores, which recompute the variables of the
   intermediate memory (and the procedures' memories) from the goal's own
   context. *)
let () =
  register_rule_checker
    (function
     | REquivSTrans n ->
         Some (EcPlRecheck.checker_of "equivS-trans" pf_as_equivS
                 (fun hyps es -> equivS_trans_subgoals hyps es n))
     | REquivFTrans n ->
         Some (EcPlRecheck.checker_of "equivF-trans" pf_as_equivF
                 (fun hyps ef -> equivF_trans_subgoals hyps ef n))
     | _ -> None)

(* -------------------------------------------------------------------- *)
(* Replacing the program of one side by an equivalent one (derived, no
   proof-node): [t_equivS_trans] with, on the replaced side, the relations
   "equal on the variables read by c, P and Q" ==> "equal on the variables
   of Q" (the precondition also keeping the one-sided part of P on that
   side), and P ==> Q on the other side. The two composition side conditions
   are closed on the spot. *)
let t_equivS_trans_eq side s tc =
  let env = FApi.tc1_env tc in
  let es = tc1_as_equivS tc in
  let c, m, mem_pre = match side with
    | `Left ->
      let mem_pre_ss = EcFol.split_sided (fst es.es_ml) (es_pr es) in
      let mem_pre = Option.map (fun mpre -> ss_inv_generalize_right mpre (fst es.es_mr)) mem_pre_ss in
      es.es_sl, es.es_ml, mem_pre
    | `Right ->
      let mem_pre_ss = EcFol.split_sided (fst es.es_mr) (es_pr es) in
      let mem_pre = Option.map (fun mpre -> ss_inv_generalize_left mpre (fst es.es_ml)) mem_pre_ss in
      es.es_sr, es.es_mr, mem_pre in

  let fv_pr  = EcPV.PV.fv env (fst m) (es_pr es).inv in
  let fv_po  = EcPV.PV.fv env (fst m) (es_po es).inv in
  let fv_r = EcPV.s_read env c in
  let ml, mr = (fst es.es_ml), (fst es.es_mr) in
  let mk_eqs fv =
    let vfv, gfv = EcPV.PV.elements fv in
    let xl x ty = ss_inv_generalize_right (f_pvar x ty ml) mr in
    let xr x ty = ss_inv_generalize_left (f_pvar x ty mr) ml in
    let veq = List.map (fun (x,ty) -> map_ts_inv2 f_eq (xl x ty) (xr x ty)) vfv in
    let geq = List.map (fun mp -> ts_inv_eqglob mp ml mp mr) gfv in
    map_ts_inv ~ml ~mr f_ands (veq @ geq) in
  let pre = mk_eqs (EcPV.PV.union (EcPV.PV.union fv_pr fv_po) fv_r) in
  let pre = map_ts_inv2 f_and pre (odfl {ml=pre.ml;mr=pre.mr;inv=f_true} mem_pre) in
  let post = mk_eqs fv_po in
  let (p1, q1), (p2, q2) =
    if side = `Left then (pre, post), (es_pr es, es_po es)
    else (es_pr es, es_po es), (pre, post)
  in

  let exists_subtac (tc : tcenv1) =
    (* Ideally these are guaranteed fresh *)
    let pl = EcIdent.create "&p__1" in
    let pr = EcIdent.create "&p__2" in
    let h  = EcIdent.create "__" in
    let tc = EcLowGoal.t_intros_i_1 [pl; pr; h] tc in
    let goal = FApi.tc1_goal tc in

    let p = match side with | `Left -> pl | `Right -> pr in
    let b = match side with | `Left -> true | `Right -> false in

    let handle_exists () =
      (* Pairing up the correct variables for the exists intro *)
      let vs, fm = EcFol.destr_exists goal in
      let eqs_pre, _ =
        let l, r = EcFol.destr_and fm in
        if b then l, r else r, l
      in
      let eqs, _ = destr_and eqs_pre in
      let eqs = destr_ands ~deep:false eqs in
      let doit eq =
        let l, r = EcFol.destr_eq eq in
        let l, r = if b then r, l else l, r in
        let v = EcFol.destr_local l in
        v, r
      in
      let eqs = List.map doit eqs in
      let exvs =
        List.map
          (fun (id, _) ->
            let v = List.assoc id eqs in
            Fsubst.f_subst_mem (EcMemory.memory m) p v)
          vs
      in

      FApi.as_tcenv1 (EcLowGoal.t_exists_intro_s (List.map paformula exvs) tc)
    in

    let tc =
      if EcFol.is_exists goal then
        handle_exists ()
      else
        tc
    in

    FApi.t_seq
      (EcLowGoal.t_generalize_hyp ?clear:(Some `Yes) h)
      EcHiGoal.process_done
      tc
  in

  FApi.t_seqsub
    (t_equivS_trans
       { est_mt   = EcMemory.memtype m; est_stmt  = s;
         est_pre1 = p1; est_post1 = q1; est_pre2 = p2; est_post2 = q2; })
    [exists_subtac; EcHiGoal.process_done; EcLowGoal.t_id; EcLowGoal.t_id]
    tc

(* -------------------------------------------------------------------- *)
(* Elaboration: the goal is known to be an [equivS]. The new program of the
   chosen side is typed in that side's memory; with a pattern ([replace]),
   the sub-statements it names in the current program can be used in it. *)
let process_equivS_trans ((tk, tf) : trans_info) (tc : tcenv1) =
  let side, pat, c =
    match tk, tf with
    | TKfun _, TFeq ->
        tc_error !!tc "transitivity * does not work on functions"
    | TKfun _, TFform _ ->
        tc_error_noXhl ~kinds:[`Equiv `Pred] !!tc
    | TKstmt (side, c), _ -> side, None, c
    | TKparsedStmt (side, pat, c), _ -> side, Some pat, c in

  let hyps = FApi.tc1_hyps tc in
  let es = tc1_as_equivS tc in
  let mt = snd (match side with `Left -> es.es_ml | `Right -> es.es_mr) in

  (* Translation of the stmt *)
  let map =
    match pat with
    | None -> Mstr.empty
    | Some p -> begin
      let regexpstmt = trans_block p in
      let ct = match side with `Left -> es.es_sl | `Right -> es.es_sr in
      match RegexpStmt.search regexpstmt ct.s_node with
      | None -> Mstr.empty
      | Some m -> m
    end
  in
  let c = TTC.tc1_process_prhl_stmt tc side ~map c in

  match tf with
  | TFeq ->
      t_equivS_trans_eq side c tc
  | TFform (p1, q1, p2, q2) ->
    let ml, mr = fst es.es_ml, fst es.es_mr in
    let p1, q1 =
      let hyps = LDecl.push_active_ts es.es_ml (mr, mt) hyps in
      let p1 = TTC.pf_process_form !!tc hyps tbool p1 in
      let q1 = TTC.pf_process_form !!tc hyps tbool q1 in
      {ml;mr;inv=p1}, {ml;mr;inv=q1}
    in
    let p2, q2 =
      let hyps = LDecl.push_active_ts (ml, mt) es.es_mr hyps in
      let p2 = TTC.pf_process_form !!tc hyps tbool p2 in
      let q2 = TTC.pf_process_form !!tc hyps tbool q2 in
      {ml;mr;inv=p2}, {ml;mr;inv=q2}
    in
    t_equivS_trans
      { est_mt   = mt; est_stmt  = c;
        est_pre1 = p1; est_post1 = q1; est_pre2 = p2; est_post2 = q2; } tc

(* -------------------------------------------------------------------- *)
(* Elaboration: the goal is known to be an [equivF]. The relations are typed
   in the pre / post memories of the procedures, the intermediate memory
   being that of [f]. *)
let process_equivF_trans ((tk, tf) : trans_info) (tc : tcenv1) =
  let f, (p1, q1, p2, q2) =
    match tk, tf with
    | TKfun _, TFeq ->
        tc_error !!tc "transitivity * does not work on functions"
    | TKfun f, TFform (p1, q1, p2, q2) -> f, (p1, q1, p2, q2)
    | (TKstmt _ | TKparsedStmt _), _ ->
        tc_error_noXhl ~kinds:[`Equiv `Stmt] !!tc in

  let env, hyps, _ = FApi.tc1_eflat tc in
  let ef = tc1_as_equivF tc in
  let f = EcTyping.trans_gamepath env f in
  let (_, prmt), (_, pomt) = Fun.hoareF_memenv (EcIdent.create "&dummy") f env in
  let (prml, prmr), (poml, pomr) = Fun.equivF_memenv ef.ef_ml ef.ef_mr ef.ef_fl ef.ef_fr env in
  let process ml mr fo =
    let inv = TTC.pf_process_form !!tc (LDecl.push_active_ts ml mr hyps) tbool fo in
    {ml=fst ml;mr=fst mr;inv} in
  let p1 = process prml (fst prmr, prmt) p1 in
  let q1 = process poml (fst pomr, pomt) q1 in
  let p2 = process (fst prml, prmt) prmr p2 in
  let q2 = process (fst poml, pomt) pomr q2 in
  t_equivF_trans
    { eft_f    = f;
      eft_pre1 = p1; eft_post1 = q1; eft_pre2 = p2; eft_post2 = q2; } tc
