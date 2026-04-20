(* -------------------------------------------------------------------- *)
open EcUtils
open EcAst
open EcFol
open EcCoreFol
open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* Structural rules for the delayed-coupling logic (paper §4.4).        *)

(* -------------------------------------------------------------------- *)
let split_prefix ~who tc n s =
  let nodes = s.EcAst.s_node in
  if List.length nodes < n then
    tc_error !!tc ~who
      "not enough instructions to move (%d requested, %d available)"
      n (List.length nodes);
  let pre, rest = List.takedrop n nodes in
  (EcAst.stmt pre, EcAst.stmt rest)

let split_suffix ~who tc n s =
  let nodes = s.EcAst.s_node in
  if List.length nodes < n then
    tc_error !!tc ~who
      "not enough instructions to move (%d requested, %d available)"
      n (List.length nodes);
  let (pre, last) = List.takedrop (List.length nodes - n) nodes in
  (EcAst.stmt pre, EcAst.stmt last)

let s_cat a b = EcAst.stmt (a.EcAst.s_node @ b.EcAst.s_node)

let s_empty = EcAst.stmt []

(* -------------------------------------------------------------------- *)
(* Pop (two-sided, forward):
     { phi | R1 x R2 } C1;D1 ~ C2;D2 { psi | S1 x S2 }
     -------------------------------------------------
     { phi | R1;C1 x R2;C2 } D1 ~ D2 { psi | S1 x S2 }
   Moves the first [n] instructions of both bodies into the
   corresponding delay contexts.                                        *)
let t_dc_pop_r ~n tc =
  let es = tc1_as_dcEquivS tc in
  let (cl, dl) = split_prefix ~who:"dc pop" tc n es.dces_cl in
  let (cr, dr) = split_prefix ~who:"dc pop" tc n es.dces_cr in
  let concl =
    f_dcEquivS
      (snd es.dces_ml) (snd es.dces_mr)
      (dces_pr es)
      (s_cat es.dces_rl cl) (s_cat es.dces_rr cr)
      dl dr
      (dces_po es) es.dces_sl es.dces_sr
  in
  FApi.xmutate1 tc `DCPop [concl]

let t_dc_pop n = FApi.t_low0 "dc-pop" (t_dc_pop_r ~n)

(* -------------------------------------------------------------------- *)
(* Pop_L (one-sided, forward): same as above but only on the left side. *)
let t_dc_pop_l_side_r ~side ~n tc =
  let es = tc1_as_dcEquivS tc in
  let concl =
    match side with
    | `Left ->
        let (cl, dl) = split_prefix ~who:"dc pop" tc n es.dces_cl in
        f_dcEquivS
          (snd es.dces_ml) (snd es.dces_mr)
          (dces_pr es)
          (s_cat es.dces_rl cl) es.dces_rr
          dl es.dces_cr
          (dces_po es) es.dces_sl es.dces_sr
    | `Right ->
        let (cr, dr) = split_prefix ~who:"dc pop" tc n es.dces_cr in
        f_dcEquivS
          (snd es.dces_ml) (snd es.dces_mr)
          (dces_pr es)
          es.dces_rl (s_cat es.dces_rr cr)
          es.dces_cl dr
          (dces_po es) es.dces_sl es.dces_sr
  in
  FApi.xmutate1 tc `DCPop [concl]

let t_dc_pop_side ~side n =
  FApi.t_low0 "dc-pop-side" (t_dc_pop_l_side_r ~side ~n)

(* -------------------------------------------------------------------- *)
(* Unpop (two-sided, inverse of Pop): takes last [n] instructions of
   each delay context back into the front of the corresponding body.   *)
let t_dc_unpop_r ~n tc =
  let es = tc1_as_dcEquivS tc in
  let (rl_pre, rl_suf) = split_suffix ~who:"dc unpop" tc n es.dces_rl in
  let (rr_pre, rr_suf) = split_suffix ~who:"dc unpop" tc n es.dces_rr in
  let concl =
    f_dcEquivS
      (snd es.dces_ml) (snd es.dces_mr)
      (dces_pr es)
      rl_pre rr_pre
      (s_cat rl_suf es.dces_cl) (s_cat rr_suf es.dces_cr)
      (dces_po es) es.dces_sl es.dces_sr
  in
  FApi.xmutate1 tc `DCUnpop [concl]

let t_dc_unpop n = FApi.t_low0 "dc-unpop" (t_dc_unpop_r ~n)

let t_dc_unpop_side_r ~side ~n tc =
  let es = tc1_as_dcEquivS tc in
  let concl =
    match side with
    | `Left ->
        let (rl_pre, rl_suf) = split_suffix ~who:"dc unpop" tc n es.dces_rl in
        f_dcEquivS
          (snd es.dces_ml) (snd es.dces_mr)
          (dces_pr es)
          rl_pre es.dces_rr
          (s_cat rl_suf es.dces_cl) es.dces_cr
          (dces_po es) es.dces_sl es.dces_sr
    | `Right ->
        let (rr_pre, rr_suf) = split_suffix ~who:"dc unpop" tc n es.dces_rr in
        f_dcEquivS
          (snd es.dces_ml) (snd es.dces_mr)
          (dces_pr es)
          es.dces_rl rr_pre
          es.dces_cl (s_cat rr_suf es.dces_cr)
          (dces_po es) es.dces_sl es.dces_sr
  in
  FApi.xmutate1 tc `DCUnpop [concl]

let t_dc_unpop_side ~side n =
  FApi.t_low0 "dc-unpop-side" (t_dc_unpop_side_r ~side ~n)

(* -------------------------------------------------------------------- *)
(* Push (two-sided, axiom):
                                                        Push
     { phi | R1 x R2 } C1 ~ C2 { phi | R1;C1 x R2;C2 }
   Closes the goal when its shape matches the axiom.                   *)
let t_dc_push_r tc =
  let es = tc1_as_dcEquivS tc in
  if not (f_equal (dces_pr es).inv (dces_po es).inv) then
    tc_error !!tc ~who:"dc push"
      "pre- and post-conditions must be identical for Push";
  let expected_sl = s_cat es.dces_rl es.dces_cl in
  let expected_sr = s_cat es.dces_rr es.dces_cr in
  if not (EcAst.s_equal es.dces_sl expected_sl) then
    tc_error !!tc ~who:"dc push"
      "left continuation S1 must equal R1;C1";
  if not (EcAst.s_equal es.dces_sr expected_sr) then
    tc_error !!tc ~who:"dc push"
      "right continuation S2 must equal R2;C2";
  FApi.xmutate1 tc `DCPush []

let t_dc_push = FApi.t_low0 "dc-push" t_dc_push_r

let t_dc_push_side_r ~side tc =
  let es = tc1_as_dcEquivS tc in
  if not (f_equal (dces_pr es).inv (dces_po es).inv) then
    tc_error !!tc ~who:"dc push"
      "pre- and post-conditions must be identical for Push";
  let (expected_sl, expected_sr, opp_c, opp_s) =
    match side with
    | `Left ->
        (s_cat es.dces_rl es.dces_cl, es.dces_rr, es.dces_cr, es.dces_sr)
    | `Right ->
        (es.dces_rl, s_cat es.dces_rr es.dces_cr, es.dces_cl, es.dces_sl)
  in
  (* Non-active side: must have body empty and S matching R. *)
  let _ = (expected_sl, expected_sr, opp_c, opp_s) in
  let () =
    match side with
    | `Left ->
        if not (List.is_empty es.dces_cr.EcAst.s_node) then
          tc_error !!tc ~who:"dc push"
            "right body must be empty for Push_L";
        if not (EcAst.s_equal es.dces_sl (s_cat es.dces_rl es.dces_cl)) then
          tc_error !!tc ~who:"dc push" "left continuation S1 must equal R1;C1";
        if not (EcAst.s_equal es.dces_sr es.dces_rr) then
          tc_error !!tc ~who:"dc push" "right continuation S2 must equal R2"
    | `Right ->
        if not (List.is_empty es.dces_cl.EcAst.s_node) then
          tc_error !!tc ~who:"dc push"
            "left body must be empty for Push_R";
        if not (EcAst.s_equal es.dces_sr (s_cat es.dces_rr es.dces_cr)) then
          tc_error !!tc ~who:"dc push" "right continuation S2 must equal R2;C2";
        if not (EcAst.s_equal es.dces_sl es.dces_rl) then
          tc_error !!tc ~who:"dc push" "left continuation S1 must equal R1"
  in
  FApi.xmutate1 tc `DCPushSide []

let t_dc_push_side ~side = FApi.t_low0 "dc-push-side" (t_dc_push_side_r ~side)

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
