(* -------------------------------------------------------------------- *)
open EcUtils
open EcAst
open EcFol
open EcCoreFol
open EcCoreGoal
open EcCoreModules
open EcLowPhlGoal
open EcReduction

(* -------------------------------------------------------------------- *)
(* Structural rules for the delayed-coupling logic (paper §4.4).        *)

(* -------------------------------------------------------------------- *)
let split_prefix ~who tc n s =
  let nodes = s.s_node in
  if List.length nodes < n then
    tc_error !!tc ~who
      "not enough instructions to move (%d requested, %d available)"
      n (List.length nodes);
  let pre, rest = List.takedrop n nodes in
  (EcAst.stmt pre, EcAst.stmt rest)

let split_suffix ~who tc n s =
  let nodes = s.s_node in
  if List.length nodes < n then
    tc_error !!tc ~who
      "not enough instructions to move (%d requested, %d available)"
      n (List.length nodes);
  let (pre, last) = List.takedrop (List.length nodes - n) nodes in
  (EcAst.stmt pre, EcAst.stmt last)

(* -------------------------------------------------------------------- *)
(* Push (two-sided):
     { phi | R1 x R2 } C1;D1 ~ C2;D2 { psi | S1 x S2 }
     -------------------------------------------------
     { phi | R1;C1 x R2;C2 } D1 ~ D2 { psi | S1 x S2 }
   Moves the first [n] instructions of both bodies into the
   corresponding delay contexts.                                        *)
let t_dc_push_r ~n tc =
  let es = tc1_as_dcEquivS tc in
  let (cl, dl) = split_prefix ~who:"dc push" tc n es.dces_cl in
  let (cr, dr) = split_prefix ~who:"dc push" tc n es.dces_cr in
  let concl =
    f_dcEquivS
      (snd es.dces_ml) (snd es.dces_mr)
      (dces_pr es)
      (s_seq es.dces_rl cl) (s_seq es.dces_rr cr)
      dl dr
      (dces_po es) es.dces_sl es.dces_sr
  in
  FApi.xmutate1 tc `DCPush [concl]

let t_dc_push n = FApi.t_low0 "dc-push" (t_dc_push_r ~n)

(* -------------------------------------------------------------------- *)
(* Push_L (one-sided): same as above but only on the left side. *)
let t_dc_push_l_side_r ~side ~n tc =
  let es = tc1_as_dcEquivS tc in
  let concl =
    match side with
    | `Left ->
        let (cl, dl) = split_prefix ~who:"dc pushl" tc n es.dces_cl in
        f_dcEquivS
          (snd es.dces_ml) (snd es.dces_mr)
          (dces_pr es)
          (s_seq es.dces_rl cl) es.dces_rr
          dl es.dces_cr
          (dces_po es) es.dces_sl es.dces_sr
    | `Right ->
        let (cr, dr) = split_prefix ~who:"dc pushr" tc n es.dces_cr in
        f_dcEquivS
          (snd es.dces_ml) (snd es.dces_mr)
          (dces_pr es)
          es.dces_rl (s_seq es.dces_rr cr)
          es.dces_cl dr
          (dces_po es) es.dces_sl es.dces_sr
  in
  FApi.xmutate1 tc `DCPushSide [concl]

let t_dc_push_side ~side n =
  FApi.t_low0 "dc-push-side" (t_dc_push_l_side_r ~side ~n)

(* -------------------------------------------------------------------- *)
(* Pop (two-sided, inverse of Push): takes last [n] instructions of
   each delay context back into the front of the corresponding body.   *)
let t_dc_pop_r ~n tc =
  let es = tc1_as_dcEquivS tc in
  let (rl_pre, rl_suf) = split_suffix ~who:"dc pop" tc n es.dces_rl in
  let (rr_pre, rr_suf) = split_suffix ~who:"dc pop" tc n es.dces_rr in
  let concl =
    f_dcEquivS
      (snd es.dces_ml) (snd es.dces_mr)
      (dces_pr es)
      rl_pre rr_pre
      (s_seq rl_suf es.dces_cl) (s_seq rr_suf es.dces_cr)
      (dces_po es) es.dces_sl es.dces_sr
  in
  FApi.xmutate1 tc `DCPop [concl]

let t_dc_pop n = FApi.t_low0 "dc-pop" (t_dc_pop_r ~n)

let t_dc_pop_side_r ~side ~n tc =
  let es = tc1_as_dcEquivS tc in
  let concl =
    match side with
    | `Left ->
        let (rl_pre, rl_suf) = split_suffix ~who:"dc popl" tc n es.dces_rl in
        f_dcEquivS
          (snd es.dces_ml) (snd es.dces_mr)
          (dces_pr es)
          rl_pre es.dces_rr
          (s_seq rl_suf es.dces_cl) es.dces_cr
          (dces_po es) es.dces_sl es.dces_sr
    | `Right ->
        let (rr_pre, rr_suf) = split_suffix ~who:"dc popr" tc n es.dces_rr in
        f_dcEquivS
          (snd es.dces_ml) (snd es.dces_mr)
          (dces_pr es)
          es.dces_rl rr_pre
          es.dces_cl (s_seq rr_suf es.dces_cr)
          (dces_po es) es.dces_sl es.dces_sr
  in
  FApi.xmutate1 tc `DCPopSide [concl]

let t_dc_pop_side ~side n =
  FApi.t_low0 "dc-pop-side" (t_dc_pop_side_r ~side ~n)

(* -------------------------------------------------------------------- *)
(* Delay (two-sided, with builtin framing):
    forall m1 m2, phi m1 m2 => psi m1 m2
    -------------------------------------------------  Delay
    { phi | R1 x R2 } C1 ~ C2 { psi | R1;C1 x R2;C2 }
*)
let t_dc_delay_r tc =
    let env = FApi.tc1_env tc in
    let es = tc1_as_dcEquivS tc in
    if not (EqTest.for_stmt env (s_seq es.dces_rl es.dces_cl) es.dces_sl) then
        tc_error !!tc ~who:"dc delay" "left post-stack must be left pre-stack and body";
    if not (EqTest.for_stmt env (s_seq es.dces_rr es.dces_cr) es.dces_sr) then
        tc_error !!tc ~who:"dc delay" "right post-stack must be right pre-stack and body";
    let concl = map_ts_inv2 f_imp (dces_pr es) (dces_po es) in
    let concl = EcSubst.f_forall_mems_ts_inv es.dces_ml es.dces_mr concl in
    FApi.xmutate1 tc `DCDelay [concl]

let t_dc_delay = FApi.t_low0 "dc-delay" t_dc_delay_r

(* -------------------------------------------------------------------- *)
(* Delay (one-sided, with builtin framing):
    forall m1 m2, phi m1 m2 => psi m1 m2
    -------------------------------------------------  Delay_L
    { phi | R1 x R2 } C1 ~ eps { psi | R1;C1 x R2 }
*)
let t_dc_delay_side_r ~side tc =
    let env = FApi.tc1_env tc in
    let es = tc1_as_dcEquivS tc in
    let r1, r2, c1, eps, s1, s2, left, right = 
        match side with
        | `Left ->
            es.dces_rl, es.dces_rr, es.dces_cl, es.dces_cr, es.dces_sl, es.dces_sr, "left", "right"
        | `Right ->
            es.dces_rr, es.dces_rl, es.dces_cr, es.dces_cl, es.dces_sr, es.dces_sl, "right", "left"
    in
    let who = "dc delay " ^ left in
    if not (List.is_empty eps.s_node) then
        tc_error !!tc ~who "%s body must be empty" right;
    if not (EqTest.for_stmt env r2 s2) then
        tc_error !!tc ~who "%s post-stack must the same as %s pre-stack" right right;
    if not (EqTest.for_stmt env (s_seq r1 c1) s1) then
        tc_error !!tc ~who "%s post-stack must the same as %s pre-stack and body" left left;
    let concl = map_ts_inv2 f_imp (dces_pr es) (dces_po es) in
    let concl = EcSubst.f_forall_mems_ts_inv es.dces_ml es.dces_mr concl in
    FApi.xmutate1 tc `DCDelaySide [concl]

let t_dc_delay_side ~side = FApi.t_low0 "dc-delay-side" (t_dc_delay_side_r ~side)

(* -------------------------------------------------------------------- *)
(* Delay* (one-sided, framed):
    forall m1 m2, phi m1 m2 => phi1 m1
    forall m1 m2, phi m1 m2 => psi m1 m2
    { ={Read(R1) U Read(C1) U Read(S1)} /\ phi1 | R1 x _ }
       C1 ~ S1
    { ={Write(R1) U Write(C1) U Write(S1)} | S1 x S2 }
    -------------------------------------------------  Delay*_L
    { phi | R1 x R2 } C1 ~ eps { psi | S1 x R2 }
*)
let t_dc_delay_star_r ~side ?inv tc =
    let env = FApi.tc1_env tc in
    let es = tc1_as_dcEquivS tc in

    let ml, mr, r1, r2, c1, eps, s1, s2, left, right = 
        match side with
        | `Left ->
            es.dces_ml, es.dces_mr, es.dces_rl, es.dces_rr, es.dces_cl,
            es.dces_cr, es.dces_sl, es.dces_sr, "left", "right"
        | `Right ->
            es.dces_mr, es.dces_ml, es.dces_rr, es.dces_rl, es.dces_cr,
            es.dces_cl, es.dces_sr, es.dces_sl, "right", "left"
    in
    let who = "dc delay " ^ left in
    if not (List.is_empty eps.s_node) then
        tc_error !!tc ~who "%s body must be empty" right;
    if not (EqTest.for_stmt env r2 s2) then
        tc_error !!tc ~who "%s post-stack must the same as %s pre-stack" right right;

    let reads = EcPV.s_read env r1 in
    let reads = EcPV.PV.union reads (EcPV.s_read env c1) in
    let reads = EcPV.PV.union reads (EcPV.s_read env s1) in

    let writes = EcPV.s_write env r1 in
    let writes = EcPV.PV.union writes (EcPV.s_write env c1) in
    let writes = EcPV.PV.union writes (EcPV.s_write env s1) in

    let mk_eqs fv =
        let vfv, gfv = EcPV.PV.elements fv in
        let ml, mr = fst ml, fst mr in
        let xl x ty = ss_inv_generalize_right (f_pvar x ty ml) mr in
        let xr x ty = ss_inv_generalize_left (f_pvar x ty mr) ml in
        let veq = List.map (fun (x,ty) -> map_ts_inv2 f_eq (xl x ty) (xr x ty)) vfv in
        let geq = List.map (fun mp -> ts_inv_eqglob mp ml mp mr) gfv in
        map_ts_inv ~ml ~mr f_ands (veq @ geq)
    in

    let pre = mk_eqs reads in
    let inv' = odfl { m=pre.ml; inv=f_true; } inv in 
    let pre = map_ts_inv2 f_and_simpl pre (ss_inv_generalize_right inv' pre.mr) in
    let post = mk_eqs writes in
    let equiv = f_dcEquivS (snd ml) (snd ml) pre r1 s_empty c1 s1 post s_empty s_empty in

    let frame = map_ts_inv2 f_imp (dces_pr es) (dces_po es) in
    let frame = EcSubst.f_forall_mems_ts_inv es.dces_ml es.dces_mr frame in

    let goals = [frame; equiv] in
    let goals =
        match inv with
        | None -> goals
        | Some inv ->
            let inv_ts = 
                match side with
                | `Left -> ss_inv_generalize_right inv (fst es.dces_mr)
                | `Right -> ss_inv_generalize_left inv (fst es.dces_ml)
            in
            let frame_equiv = map_ts_inv2 f_imp (dces_pr es) inv_ts in
            let frame_equiv = EcSubst.f_forall_mems_ts_inv es.dces_ml es.dces_mr frame_equiv in
            frame_equiv :: goals
    in

    FApi.xmutate1 tc `DCDelayStar goals

let t_dc_delay_star ~side ?inv = FApi.t_low0 "dc-delay-star" (t_dc_delay_star_r ~side ?inv)

(* -------------------------------------------------------------------- *)
(* Conseq:
     phi ==> phi'   psi' ==> psi
     { phi' | R1 x R2 } C1 ~ C2 { psi' | S1 x S2 }
     ------------------------------------------------
     { phi | R1 x R2 } C1 ~ C2 { psi | S1 x S2 }
   We implement the simple form where R_i and S_i are preserved and
   only pre/post are weakened.                                          *)
let t_dc_conseq_r ~pre ~post tc =
  let es = tc1_as_dcEquivS tc in
  let pre_f  = pre.inv in
  let post_f = post.inv in
  (* Assume pre and post are expressed over the judgment's memories. *)
  let concl_mid =
    f_dcEquivS
      (snd es.dces_ml) (snd es.dces_mr)
      pre
      es.dces_rl es.dces_rr es.dces_cl es.dces_cr
      post es.dces_sl es.dces_sr
  in
  let ml = fst es.dces_ml in
  let mr = fst es.dces_mr in
  let side_imp f1 f2 =
    let imp = f_imp f1 f2 in
    EcSubst.f_forall_mems_ts_inv es.dces_ml es.dces_mr { ml; mr; inv = imp }
  in
  let goal_pre  = side_imp (dces_pr es).inv pre_f in
  let goal_post = side_imp post_f (dces_po es).inv in
  FApi.xmutate1 tc `DCConseq [goal_pre; goal_post; concl_mid]

let t_dc_conseq ~pre ~post =
  FApi.t_low0 "dc-conseq" (t_dc_conseq_r ~pre ~post)

(* -------------------------------------------------------------------- *)
(* Case:
     { phi /\ theta | R1xR2 } C1 ~ C2 { psi | S1xS2 }
     { phi /\ ~theta | R1xR2 } C1 ~ C2 { psi | S1xS2 }
     -------------------------------------------------  Case
     { phi | R1xR2 } C1 ~ C2 { psi | S1xS2 }
*)
let t_dc_case_r theta tc =
  let es = tc1_as_dcEquivS tc in
  let theta_ts : ts_inv =
    { ml = fst es.dces_ml; mr = fst es.dces_mr; inv = theta }
  in
  let pr_and_theta =
    map_ts_inv2 f_and_simpl (dces_pr es) theta_ts
  in
  let pr_and_not_theta =
    map_ts_inv2 f_and_simpl (dces_pr es) (map_ts_inv1 f_not_simpl theta_ts)
  in
  let build pr =
    f_dcEquivS
      (snd es.dces_ml) (snd es.dces_mr)
      pr
      es.dces_rl es.dces_rr es.dces_cl es.dces_cr
      (dces_po es) es.dces_sl es.dces_sr
  in
  FApi.xmutate1 tc `DCCase
    [ build pr_and_theta; build pr_and_not_theta ]

let t_dc_case theta = FApi.t_low0 "dc-case" (t_dc_case_r theta)

(* -------------------------------------------------------------------- *)
(* Frame:
     { phi | R1xR2 } C1 ~ C2 { psi | S1xS2 }
     Fv(theta) disjoint from Write(R1;C1) on &1
     Fv(theta) disjoint from Write(R2;C2) on &2
     ----------------------------------------------- Frame
     { phi /\ theta | R1xR2 } C1 ~ C2 { psi /\ theta | S1xS2 }
*)
let t_dc_frame_r theta tc =
  let es = tc1_as_dcEquivS tc in
  let env = FApi.tc1_env tc in
  let ml = fst es.dces_ml in
  let mr = fst es.dces_mr in

  let fv_l = EcPV.PV.fv env ml theta in
  let fv_r = EcPV.PV.fv env mr theta in

  let write_l =
    EcPV.PV.union (EcPV.s_write env es.dces_rl)
                  (EcPV.s_write env es.dces_cl) in
  let write_r =
    EcPV.PV.union (EcPV.s_write env es.dces_rr)
                  (EcPV.s_write env es.dces_cr) in

  if not (EcPV.PV.indep env fv_l write_l) then
    tc_error !!tc ~who:"dc frame"
      "Fv(theta) at &1 intersects Write(R1;C1)";
  if not (EcPV.PV.indep env fv_r write_r) then
    tc_error !!tc ~who:"dc frame"
      "Fv(theta) at &2 intersects Write(R2;C2)";

  let theta_ts : ts_inv = { ml; mr; inv = theta } in
  let new_pre  = map_ts_inv2 f_and_simpl (dces_pr es) theta_ts in
  let new_post = map_ts_inv2 f_and_simpl (dces_po es) theta_ts in
  let concl =
    f_dcEquivS
      (snd es.dces_ml) (snd es.dces_mr)
      new_pre
      es.dces_rl es.dces_rr es.dces_cl es.dces_cr
      new_post es.dces_sl es.dces_sr
  in
  FApi.xmutate1 tc `DCFrame [concl]

let t_dc_frame theta = FApi.t_low0 "dc-frame" (t_dc_frame_r theta)

(* -------------------------------------------------------------------- *)
(* Indep:
     { phi | R1xR2 } C1 ~ C2 { psi | S1xS2 }
     Write(Ci) ⊥ Read(Ti)    Read(Ci) ⊥ Write(Ti)
     --------------------------------------------- Indep
     { phi | R1;T1 x R2;T2 } C1 ~ C2 { psi | S1;T1 x S2;T2 }

   T_i is identified by its length: the user supplies [nl] (left)
   and [nr] (right) so that T1 = suffix-of-length-[nl] of R1 = of S1,
   and similarly on the right. The tactic then checks Read/Write
   disjointness via EcPV.                                              *)
let t_dc_indep_r ~nl ~nr tc =
  let es = tc1_as_dcEquivS tc in
  let env = FApi.tc1_env tc in

  let (rl_pre, t1_from_r) =
    split_suffix ~who:"dc indep" tc nl es.dces_rl in
  let (sl_pre, t1_from_s) =
    split_suffix ~who:"dc indep" tc nl es.dces_sl in
  if not (EcAst.s_equal t1_from_r t1_from_s) then
    tc_error !!tc ~who:"dc indep"
      "the suffix of R1 must equal the suffix of S1 (of length %d)" nl;

  let (rr_pre, t2_from_r) =
    split_suffix ~who:"dc indep" tc nr es.dces_rr in
  let (sr_pre, t2_from_s) =
    split_suffix ~who:"dc indep" tc nr es.dces_sr in
  if not (EcAst.s_equal t2_from_r t2_from_s) then
    tc_error !!tc ~who:"dc indep"
      "the suffix of R2 must equal the suffix of S2 (of length %d)" nr;

  let t1 = t1_from_r in
  let t2 = t2_from_r in

  let wc1 = EcPV.s_write env es.dces_cl in
  let rc1 = EcPV.s_read  env es.dces_cl in
  let wt1 = EcPV.s_write env t1 in
  let rt1 = EcPV.s_read  env t1 in
  let wc2 = EcPV.s_write env es.dces_cr in
  let rc2 = EcPV.s_read  env es.dces_cr in
  let wt2 = EcPV.s_write env t2 in
  let rt2 = EcPV.s_read  env t2 in

  if not (EcPV.PV.indep env wc1 rt1) then
    tc_error !!tc ~who:"dc indep"
      "Write(C1) and Read(T1) are not disjoint";
  if not (EcPV.PV.indep env rc1 wt1) then
    tc_error !!tc ~who:"dc indep"
      "Read(C1) and Write(T1) are not disjoint";
  if not (EcPV.PV.indep env wc2 rt2) then
    tc_error !!tc ~who:"dc indep"
      "Write(C2) and Read(T2) are not disjoint";
  if not (EcPV.PV.indep env rc2 wt2) then
    tc_error !!tc ~who:"dc indep"
      "Read(C2) and Write(T2) are not disjoint";

  let concl =
    f_dcEquivS
      (snd es.dces_ml) (snd es.dces_mr)
      (dces_pr es)
      rl_pre rr_pre es.dces_cl es.dces_cr
      (dces_po es) sl_pre sr_pre
  in
  FApi.xmutate1 tc `DCIndep [concl]

let t_dc_indep ~nl ~nr =
  FApi.t_low0 "dc-indep" (t_dc_indep_r ~nl ~nr)

let t_dc_trans_r p12 q12 p23 q23 m r2 c2 s2 tc =
    let es = tc1_as_dcEquivS tc in
    let env = FApi.tc1_env tc in
    let hyps = FApi.tc1_hyps tc in

    let dc12 =
        f_dcEquivS
            (snd es.dces_ml) (snd m)
            p12 es.dces_rl r2 es.dces_cl c2
            q12 es.dces_sl s2
    in
    let dc23 =
        f_dcEquivS
            (snd m) (snd es.dces_mr)
            p23 r2 es.dces_rr c2 es.dces_cr
            q23 s2 es.dces_sr
    in
    let open EcPV in
    let open EcEnv in

    let pre = dces_pr es in
    let post = dces_po es in

    let frame_pre =
        (* Compute the intermediate program variables *)
        let fv1 = PV.fv env p12.mr p12.inv in
        let fv2 = PV.fv env p23.ml p23.inv in
        let fv  = PV.union fv1 fv2 in
        let elts, glob = PV.ntr_elements fv in

        let bd, s = generalize_subst env (fst m) elts glob in
        let s = PVM.of_mpv s (fst m) in
        let concl = {ml = p12.ml; mr = p23.mr; inv = f_and (PVM.subst env s p12.inv) (PVM.subst env s p23.inv); } in
        EcSubst.f_forall_mems_ts_inv es.dces_ml es.dces_mr (map_ts_inv2 f_imp pre (map_ts_inv1 (f_exists bd) concl))
    in 

    let frame_post =
        let m2 = LDecl.fresh_id hyps "&m" in
        assert (post.ml = q12.ml && post.mr = q23.mr);
        let q1 = (EcSubst.ts_inv_rebind_right q12 m2).inv in
        let q2 = (EcSubst.ts_inv_rebind_left q23 m2).inv in
        f_forall_mems [es.dces_ml; (m2, snd m); es.dces_mr] (f_imps [q1;q2] post.inv)
    in
    FApi.xmutate1 tc `DCTrans [frame_pre; frame_post; dc12; dc23]

let t_dc_trans p12 q12 p23 q23 m r2 c2 s2 =
  FApi.t_low0 "dc-indep" (t_dc_trans_r p12 q12 p23 q23 m r2 c2 s2)
