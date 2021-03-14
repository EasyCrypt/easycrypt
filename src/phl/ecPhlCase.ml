(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* --------------------------------------------------------------------- *)
open EcFol
open EcCoreGoal
open EcLowPhlGoal

(* --------------------------------------------------------------------- *)
let t_hoare_case_r f tc =
  let hs = tc1_as_hoareS tc in
  let concl1 = f_hoareS_r { hs with hs_pr = f_and_simpl hs.hs_pr f } in
  let concl2 = f_hoareS_r { hs with hs_pr = f_and_simpl hs.hs_pr (f_not f) } in
  FApi.xmutate1 tc (`HlCase f) [concl1; concl2]

(* --------------------------------------------------------------------- *)
let t_choare_case_r f tc =
  let chs = tc1_as_choareS tc in
  let concl1 = f_cHoareS_r
    { chs with chs_pr = f_and_simpl chs.chs_pr f } in
  let concl2 = f_cHoareS_r
    { chs with chs_pr = f_and_simpl chs.chs_pr (f_not f) } in
  FApi.xmutate1 tc (`HlCase f) [concl1; concl2]

(* --------------------------------------------------------------------- *)
let t_bdhoare_case_r f tc =
  let bhs = tc1_as_bdhoareS tc in
  let concl1 = f_bdHoareS_r
    { bhs with bhs_pr = f_and_simpl bhs.bhs_pr f } in
  let concl2 = f_bdHoareS_r
    { bhs with bhs_pr = f_and_simpl bhs.bhs_pr (f_not f) } in
  FApi.xmutate1 tc (`HlCase f) [concl1; concl2]

(* --------------------------------------------------------------------- *)
let t_equiv_case_r f tc =
  let es = tc1_as_equivS tc in
  (* FIXME quantum: is it needed ? *)
  EcQuantum.check_classical (FApi.tc1_env tc) f;
  let concl1 = f_equivS_r { es with es_pr = f_and es.es_pr f } in
  let concl2 = f_equivS_r { es with es_pr = f_and es.es_pr (f_not f) } in
  FApi.xmutate1 tc (`HlCase f) [concl1; concl2]

(* --------------------------------------------------------------------- *)
let t_hoare_case   = FApi.t_low1 "hoare-case"   t_hoare_case_r
let t_choare_case  = FApi.t_low1 "choare-case"  t_choare_case_r
let t_bdhoare_case = FApi.t_low1 "bdhoare-case" t_bdhoare_case_r
let t_equiv_case   = FApi.t_low1 "equiv-case"   t_equiv_case_r

(* --------------------------------------------------------------------- *)
let t_hl_case_r f tc =
  t_hS_or_chS_or_bhS_or_eS
    ~th:(t_hoare_case f)
    ~tch:(t_choare_case f)
    ~tbh:(t_bdhoare_case f)
    ~te:(t_equiv_case f)
    tc

(* -------------------------------------------------------------------- *)
let t_hl_case = FApi.t_low1 "hl-case" t_hl_case_r
