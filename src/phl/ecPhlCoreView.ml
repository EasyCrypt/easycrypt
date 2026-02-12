(* -------------------------------------------------------------------- *)
open EcFol

open EcCoreGoal
open EcLowPhlGoal
open EcAst

(* -------------------------------------------------------------------- *)
let t_hoare_of_bdhoareS_r tc =
  let bhs = tc1_as_bdhoareS tc in
  if not (bhs.bhs_cmp = FHeq && f_equal (bhs_bd bhs).inv f_r0) then
    tc_error !!tc "%s" "bound must be equal to 0%r";
  let post = (map_ss_inv1 f_not (bhs_po bhs)) in
  let concl =
    f_hoareS (
      snd bhs.bhs_m)
      (bhs_pr bhs)
      bhs.bhs_s
      {hsi_m=post.m;hsi_inv=empty_poe post.inv}
  in
  FApi.xmutate1 tc `ViewBdHoare [concl]

(* -------------------------------------------------------------------- *)
let t_hoare_of_bdhoareF_r tc =
  let bhf = tc1_as_bdhoareF tc in
  if not (bhf.bhf_cmp = FHeq && f_equal (bhf_bd bhf).inv f_r0) then
    tc_error !!tc "%s" "bound must be equal to 0%r";
  let post = map_ss_inv1 f_not (bhf_po bhf) in
  let concl =
    f_hoareF (bhf_pr bhf) bhf.bhf_f {hsi_m=post.m;hsi_inv=empty_poe post.inv}
  in
  FApi.xmutate1 tc `ViewBdHoare [concl]

(* -------------------------------------------------------------------- *)
let t_bdhoare_of_hoareS_r tc =
  let hs = tc1_as_hoareS tc in
  let (inv,_,_) as post = (hs_po hs).hsi_inv in
  if not (is_empty_poe post) then
    tc_error !!tc "Exceptions are not permitted";
  let m = (hs_po hs).hsi_m in
  let concl =
    f_bdHoareS (snd hs.hs_m) (hs_pr hs) hs.hs_s (map_ss_inv1 f_not {m;inv}) FHeq {m=fst hs.hs_m;inv=f_r0}
  in
  FApi.xmutate1 tc `ViewBdHoare [concl]

(* -------------------------------------------------------------------- *)
let t_bdhoare_of_hoareF_r tc =
  let hf = tc1_as_hoareF tc in
  let (inv,_,_) as post = (hf_po hf).hsi_inv in
  if not (is_empty_poe post) then
    tc_error !!tc "Exceptions are not permitted";
  let m = (hf_po hf).hsi_m in
  let concl =
    f_bdHoareF (hf_pr hf) hf.hf_f (map_ss_inv1 f_not {m;inv}) FHeq {m=hf.hf_m;inv=f_r0} in
  FApi.xmutate1 tc `ViewBdHoare [concl]

(* -------------------------------------------------------------------- *)
let t_hoare_of_bdhoareS = FApi.t_low0 "hoare-bdhoareS" t_hoare_of_bdhoareS_r
let t_hoare_of_bdhoareF = FApi.t_low0 "hoare-bdhoareF" t_hoare_of_bdhoareF_r
let t_bdhoare_of_hoareS = FApi.t_low0 "bdhoare-hoareS" t_bdhoare_of_hoareS_r
let t_bdhoare_of_hoareF = FApi.t_low0 "bdhoare-hoareF" t_bdhoare_of_hoareF_r
