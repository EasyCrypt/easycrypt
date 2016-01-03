(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
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
let t_bdhoare_of_hoareS_r tc =
  let hs = tc1_as_hoareS tc in
  let concl = f_bdHoareS hs.hs_m hs.hs_pr hs.hs_s (f_not hs.hs_po) FHeq f_r0 in
  FApi.xmutate1 tc `ViewBdHoare [concl]

(* -------------------------------------------------------------------- *)
let t_bdhoare_of_hoareF_r tc =
  let hf = tc1_as_hoareF tc in
  let concl = f_bdHoareF hf.hf_pr hf.hf_f (f_not hf.hf_po) FHeq f_r0 in
  FApi.xmutate1 tc `ViewBdHoare [concl]

(* -------------------------------------------------------------------- *)
let t_hoare_of_bdhoareS = FApi.t_low0 "hoare-bdhoareS" t_hoare_of_bdhoareS_r
let t_hoare_of_bdhoareF = FApi.t_low0 "hoare-bdhoareF" t_hoare_of_bdhoareF_r
let t_bdhoare_of_hoareS = FApi.t_low0 "bdhoare-hoareS" t_bdhoare_of_hoareS_r
let t_bdhoare_of_hoareF = FApi.t_low0 "bdhoare-hoareF" t_bdhoare_of_hoareF_r
