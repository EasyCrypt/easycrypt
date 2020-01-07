(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcFol

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
let t_hoare_of_bdhoareS_r tc =
  let bhs = tc1_as_bdhoareS tc in
  if not (bhs.bhs_cmp = FHeq && f_equal bhs.bhs_bd f_r0) then
    tc_error !!tc "%s" "bound must be equal to 0%r";
  let concl = f_hoareS bhs.bhs_m bhs.bhs_pr bhs.bhs_s (f_not bhs.bhs_po) in
  FApi.xmutate1 tc `ViewBdHoare [concl]

(* -------------------------------------------------------------------- *)
let t_hoare_of_bdhoareF_r tc =
  let bhf = tc1_as_bdhoareF tc in
  if not (bhf.bhf_cmp = FHeq && f_equal bhf.bhf_bd f_r0) then
    tc_error !!tc "%s" "bound must be equal to 0%r";
  let concl = f_hoareF bhf.bhf_pr bhf.bhf_f (f_not bhf.bhf_po) in
  FApi.xmutate1 tc `ViewBdHoare [concl]

(* -------------------------------------------------------------------- *)
let t_hoare_of_choareS_r tc =
  let chs = tc1_as_choareS tc in
  if not (f_equal chs.chs_c f_eint_infty) then
    tc_error !!tc "%s" "time bound must be equal to +infinity";
  let concl = f_hoareS chs.chs_m chs.chs_pr chs.chs_s chs.chs_po in
  FApi.xmutate1 tc `ViewCHoare [concl]

(* -------------------------------------------------------------------- *)
let t_hoare_of_choareF_r tc =
  let chf = tc1_as_choareF tc in
  if not (f_equal chf.chf_c f_eint_infty) then
    tc_error !!tc "%s" "bound must be equal to +infinity";
  let concl = f_hoareF chf.chf_pr chf.chf_f chf.chf_po in
  FApi.xmutate1 tc `ViewCHoare [concl]

(* -------------------------------------------------------------------- *)
let t_bdhoare_of_hoareS_r tc =
  let hs = tc1_as_hoareS tc in
  let concl = f_bdHoareS hs.shs_m hs.shs_pr hs.shs_s (f_not hs.shs_po) FHeq f_r0 in
  FApi.xmutate1 tc `ViewBdHoare [concl]

(* -------------------------------------------------------------------- *)
let t_bdhoare_of_hoareF_r tc =
  let hf = tc1_as_hoareF tc in
  let concl = f_bdHoareF hf.shf_pr hf.shf_f (f_not hf.shf_po) FHeq f_r0 in
  FApi.xmutate1 tc `ViewBdHoare [concl]

(* -------------------------------------------------------------------- *)
let t_choare_of_hoareS_r tc =
  let hs = tc1_as_hoareS tc in
  let concl = f_cHoareS hs.shs_m hs.shs_pr hs.shs_s hs.shs_po f_eint_infty in
  FApi.xmutate1 tc `ViewCHoare [concl]

(* -------------------------------------------------------------------- *)
let t_choare_of_hoareF_r tc =
  let hf = tc1_as_hoareF tc in
  let concl = f_cHoareF hf.shf_pr hf.shf_f hf.shf_po f_eint_infty in
  FApi.xmutate1 tc `ViewCHoare [concl]

(* -------------------------------------------------------------------- *)
let t_hoare_of_bdhoareS = FApi.t_low0 "hoare-bdhoareS" t_hoare_of_bdhoareS_r
let t_hoare_of_bdhoareF = FApi.t_low0 "hoare-bdhoareF" t_hoare_of_bdhoareF_r
let t_hoare_of_choareS  = FApi.t_low0 "hoare-choareS"  t_hoare_of_choareS_r
let t_hoare_of_choareF  = FApi.t_low0 "hoare-choareF"  t_hoare_of_choareF_r
let t_bdhoare_of_hoareS = FApi.t_low0 "bdhoare-hoareS" t_bdhoare_of_hoareS_r
let t_bdhoare_of_hoareF = FApi.t_low0 "bdhoare-hoareF" t_bdhoare_of_hoareF_r
let t_choare_of_hoareS  = FApi.t_low0 "choare-hoareS"  t_choare_of_hoareS_r
let t_choare_of_hoareF  = FApi.t_low0 "choare-hoareF"  t_choare_of_hoareF_r
