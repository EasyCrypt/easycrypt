(* -------------------------------------------------------------------- *)
open EcAst
open EcFol

open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal

open EcPhlCoreView
open EcPhlConseq

module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
(* The top-level tactic                                                 *)
let t_hoare_bd_hoare tc =
  let concl = FApi.tc1_goal tc in

  match concl.f_node with
  | FbdHoareF bhf ->
    if   bhf.bhf_cmp = FHeq && f_equal (bhf_bd bhf).inv f_r0
    then t_hoare_of_bdhoareF tc
    else
      FApi.t_seqsub
        (t_bdHoareF_conseq_bd FHeq {m=bhf.bhf_m; inv=f_r0})
        [FApi.t_try EcPhlAuto.t_pl_trivial; t_hoare_of_bdhoareF]
        tc

  | FbdHoareS bhs ->
    if   bhs.bhs_cmp = FHeq && f_equal (bhs_bd bhs).inv f_r0
    then t_hoare_of_bdhoareS tc
    else
      FApi.t_seqsub
        (t_bdHoareS_conseq_bd FHeq {m=fst bhs.bhs_m; inv=f_r0})
        [FApi.t_try EcPhlAuto.t_pl_trivial; t_hoare_of_bdhoareS]
        tc

  | FhoareF _ -> t_bdhoare_of_hoareF tc
  | FhoareS _ -> t_bdhoare_of_hoareS tc

  | _ -> tc_error !!tc "a hoare or phoare judgment was expected"

(* -------------------------------------------------------------------- *)
type 'a split_t = {
  as_bdh : proofenv -> form -> 'a * ss_inv * hoarecmp * ss_inv;
  mk_bdh : 'a * ss_inv * hoarecmp * ss_inv -> form;
}

type 'a destr_t = {
  as_bop : proofenv -> ss_inv -> ss_inv * ss_inv;
  mk_bop : ss_inv -> ss_inv -> ss_inv;
}

(* -------------------------------------------------------------------- *)
let t_bdhoare_split_bop sp dt b1 b2 b3 tc =
  let concl = FApi.tc1_goal tc in
  let bh, po, cmp, bd = sp.as_bdh !!tc concl in
  let a, b = dt.as_bop !!tc po in

  let g1 = sp.mk_bdh (bh, a, cmp, b1) in
  let g2 = sp.mk_bdh (bh, b, cmp, b2) in
  let g3 = sp.mk_bdh (bh, dt.mk_bop a b, hoarecmp_opp cmp, b3) in
  let nb = map_ss_inv2 f_real_sub (map_ss_inv2 f_real_add b1 b2) b3 in

  assert (f_equal nb.inv bd.inv);
  FApi.xmutate1 tc `BdHoareSplit [g1; g2; g3]

(* -------------------------------------------------------------------- *)
let t_bdhoare_split_bop_conseq t_conseq_bd sp dt b1 b2 b3 tc =
  let concl = FApi.tc1_goal tc in
  let _, _, cmp, b = sp.as_bdh !!tc concl in
  let nb = map_ss_inv2 f_real_sub (map_ss_inv2 f_real_add b1 b2) b3 in
  let t_main = t_bdhoare_split_bop sp dt b1 b2 b3 in

  if   f_equal nb.inv b.inv
  then t_main tc
  else FApi.t_seqsub (t_conseq_bd cmp nb) [t_id; t_main] tc

(* -------------------------------------------------------------------- *)
let bdhoare_kind tc =
  match (FApi.tc1_goal tc).f_node with
  | FbdHoareS _ -> true
  | FbdHoareF _ -> false
  | _           -> tc_error !!tc "the conclusion should be a bdhoare judgment"

(* -------------------------------------------------------------------- *)
let gen_S tactic =
  let as_bdh pf f =
    let bh = pf_as_bdhoareS pf f in
      (bh, (bhs_po bh), bh.bhs_cmp, bhs_bd bh)

  and mk_bdh (bh, po, cmp, b) =
    f_bdHoareS (snd bh.bhs_m) (bhs_pr bh) bh.bhs_s po cmp b in

  tactic t_bdHoareS_conseq_bd { as_bdh; mk_bdh; }

(* -------------------------------------------------------------------- *)
let gen_F tactic =
  let as_bdh pf f =
    let bh = pf_as_bdhoareF pf f in
      (bh, (bhf_po bh), bh.bhf_cmp, bhf_bd bh) in

  let mk_bdh (bh, po, cmp, b) =
    f_bdHoareF (bhf_pr bh) bh.bhf_f po cmp b in

  tactic t_bdHoareF_conseq_bd { as_bdh; mk_bdh; }

(* -------------------------------------------------------------------- *)
let and_dt =
  let destr_and pf f =
    try 
      let f1 = map_ss_inv1 (fun f -> fst (destr_and f)) f in
      let f2 = map_ss_inv1 (fun f -> snd (destr_and f)) f in
      (f1, f2)
    with DestrError _ ->
      tc_error pf "the postcondition must be a conjunction"
  in
    { as_bop = destr_and; mk_bop = map_ss_inv2 f_or; }

let t_bdhoareS_and = gen_S t_bdhoare_split_bop_conseq and_dt
let t_bdhoareF_and = gen_F t_bdhoare_split_bop_conseq and_dt

let t_bdhoare_and b1 b2 b3 tc =
  if   bdhoare_kind tc
  then t_bdhoareS_and b1 b2 b3 tc
  else t_bdhoareF_and b1 b2 b3 tc

(* -------------------------------------------------------------------- *)
let or_dt =
  let destr_or pf f =
    try 
      let f1 = map_ss_inv1 (fun f -> fst (destr_or f)) f in
      let f2 = map_ss_inv1 (fun f -> snd (destr_or f)) f in
      (f1, f2)
    with DestrError _ ->
      tc_error pf "the postcondition must be a disjunction"
  in
    { as_bop = destr_or; mk_bop = map_ss_inv2 f_and; }

let t_bdhoareS_or = gen_S t_bdhoare_split_bop_conseq or_dt
let t_bdhoareF_or = gen_F t_bdhoare_split_bop_conseq or_dt

let t_bdhoare_or b1 b2 b3 tc =
  if   bdhoare_kind tc
  then t_bdhoareS_or b1 b2 b3 tc
  else t_bdhoareF_or b1 b2 b3 tc

(* -------------------------------------------------------------------- *)
let t_bdhoare_split_not split b1 b2 tc =
  let bh, po, cmp, bd = split.as_bdh !!tc (FApi.tc1_goal tc) in
  let g1 = split.mk_bdh (bh, map_ss_inv1 (fun _ -> f_true) po, cmp, b1) in
  let g2 = split.mk_bdh (bh, map_ss_inv1 f_not_simpl po, hoarecmp_opp cmp, b2) in
  let nb = map_ss_inv2 f_real_sub b1 b2 in

  assert (f_equal nb.inv bd.inv);
  FApi.xmutate1 tc `BdHoareSplit [g1; g2]

let t_bdhoare_split_not_conseq t_conseq_bd split b1 b2 tc =
  let hyps = FApi.tc1_hyps tc in
  let _, _, cmp, b = split.as_bdh !!tc (FApi.tc1_goal tc) in
  let nb = map_ss_inv2 f_real_sub b1 b2 in
  let t_main = t_bdhoare_split_not split b1 b2  in

  if EcReduction.ss_inv_alpha_eq hyps nb b
  then t_main tc
  else FApi.t_seqsub (t_conseq_bd cmp nb) [t_id; t_main] tc

(* -------------------------------------------------------------------- *)
let t_bdhoareS_not = gen_S t_bdhoare_split_not_conseq
let t_bdhoareF_not = gen_F t_bdhoare_split_not_conseq

let t_bdhoare_not b1 b2 tc =
   if   bdhoare_kind tc
   then t_bdhoareS_not b1 b2 tc
   else t_bdhoareF_not b1 b2 tc
