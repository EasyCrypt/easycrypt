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
    if   bhf.bhf_cmp = FHeq && f_equal bhf.bhf_bd f_r0
    then t_hoare_of_bdhoareF tc
    else
      FApi.t_seqsub
        (t_bdHoareF_conseq_bd FHeq f_r0)
        [FApi.t_try EcPhlAuto.t_pl_trivial; t_hoare_of_bdhoareF]
        tc

  | FbdHoareS bhs ->
    if   bhs.bhs_cmp = FHeq && f_equal bhs.bhs_bd f_r0
    then t_hoare_of_bdhoareS tc
    else
      FApi.t_seqsub
        (t_bdHoareS_conseq_bd FHeq f_r0)
        [FApi.t_try EcPhlAuto.t_pl_trivial; t_hoare_of_bdhoareS]
        tc

  | FhoareF _ -> t_bdhoare_of_hoareF tc
  | FhoareS _ -> t_bdhoare_of_hoareS tc

  | _ -> tc_error !!tc "a hoare or phoare judgment was expected"

(* -------------------------------------------------------------------- *)
type 'a split_t = {
  as_bdh : proofenv -> form -> 'a * form * hoarecmp * form;
  mk_bdh : 'a * form * hoarecmp * form -> form;
}

type 'a destr_t = {
  as_bop : proofenv -> form -> form * form;
  mk_bop : form -> form -> form;
}

(* -------------------------------------------------------------------- *)
let t_bdhoare_split_bop sp dt b1 b2 b3 tc =
  let concl = FApi.tc1_goal tc in
  let bh, po, cmp, bd = sp.as_bdh !!tc concl in
  let a, b = dt.as_bop !!tc po in

  let g1 = sp.mk_bdh (bh, a, cmp, b1) in
  let g2 = sp.mk_bdh (bh, b, cmp, b2) in
  let g3 = sp.mk_bdh (bh, dt.mk_bop a b, hoarecmp_opp cmp, b3) in
  let nb = f_real_sub (f_real_add b1 b2) b3 in

  assert (f_equal nb bd);
  FApi.xmutate1 tc `BdHoareSplit [g1; g2; g3]

(* -------------------------------------------------------------------- *)
let t_bdhoare_split_bop_conseq t_conseq_bd sp dt b1 b2 b3 tc =
  let concl = FApi.tc1_goal tc in
  let _, _, cmp, b = sp.as_bdh !!tc concl in
  let nb = f_real_sub (f_real_add b1 b2) b3 in
  let t_main = t_bdhoare_split_bop sp dt b1 b2 b3 in

  if   f_equal nb b
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
      (bh, bh.bhs_po, bh.bhs_cmp, bh.bhs_bd)

  and mk_bdh (bh, po, cmp, b) =
    f_bdHoareS_r { bh with bhs_po = po; bhs_cmp = cmp; bhs_bd = b; } in

  tactic t_bdHoareS_conseq_bd { as_bdh; mk_bdh; }

(* -------------------------------------------------------------------- *)
let gen_F tactic =
  let as_bdh pf f =
    let bh = pf_as_bdhoareF pf f in
      (bh, bh.bhf_po, bh.bhf_cmp, bh.bhf_bd)

  and mk_bdh (bh, po, cmp, b) =
    f_bdHoareF bh.bhf_pr bh.bhf_f po cmp b in

  tactic t_bdHoareF_conseq_bd { as_bdh; mk_bdh; }

(* -------------------------------------------------------------------- *)
let and_dt =
  let destr_and pf f =
    try  destr_and f
    with DestrError _ ->
      tc_error pf "the postcondition must be a conjunction"
  in
    { as_bop = destr_and; mk_bop = f_or; }

let t_bdhoareS_and = gen_S t_bdhoare_split_bop_conseq and_dt
let t_bdhoareF_and = gen_F t_bdhoare_split_bop_conseq and_dt

let t_bdhoare_and b1 b2 b3 tc =
  if   bdhoare_kind tc
  then t_bdhoareS_and b1 b2 b3 tc
  else t_bdhoareF_and b1 b2 b3 tc

(* -------------------------------------------------------------------- *)
let or_dt =
  let destr_or pf f =
    try  destr_or f
    with DestrError _ ->
      tc_error pf "the postcondition must be a disjunction"
  in
    { as_bop = destr_or; mk_bop = f_and; }

let t_bdhoareS_or = gen_S t_bdhoare_split_bop_conseq or_dt
let t_bdhoareF_or = gen_F t_bdhoare_split_bop_conseq or_dt

let t_bdhoare_or b1 b2 b3 tc =
  if   bdhoare_kind tc
  then t_bdhoareS_or b1 b2 b3 tc
  else t_bdhoareF_or b1 b2 b3 tc

(* -------------------------------------------------------------------- *)
let t_bdhoare_split_not split b1 b2 tc =
  let bh, po, cmp, bd = split.as_bdh !!tc (FApi.tc1_goal tc) in
  let g1 = split.mk_bdh (bh, f_true, cmp, b1) in
  let g2 = split.mk_bdh (bh, f_not_simpl po, hoarecmp_opp cmp, b2) in
  let nb = f_real_sub b1 b2 in

  assert (f_equal nb bd);
  FApi.xmutate1 tc `BdHoareSplit [g1; g2]

let t_bdhoare_split_not_conseq t_conseq_bd split b1 b2 tc =
  let _, _, cmp, b = split.as_bdh !!tc (FApi.tc1_goal tc) in
  let nb = f_real_sub b1 b2 in
  let t_main = t_bdhoare_split_not split b1 b2  in

  if   f_equal nb b
  then t_main tc
  else FApi.t_seqsub (t_conseq_bd cmp nb) [t_id; t_main] tc

(* -------------------------------------------------------------------- *)
let t_bdhoareS_not = gen_S t_bdhoare_split_not_conseq
let t_bdhoareF_not = gen_F t_bdhoare_split_not_conseq

let t_bdhoare_not b1 b2 tc =
   if   bdhoare_kind tc
   then t_bdhoareS_not b1 b2 tc
   else t_bdhoareF_not b1 b2 tc
