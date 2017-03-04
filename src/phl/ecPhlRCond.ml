(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2017 - Inria
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcModules
open EcFol

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
module Low = struct
  (* ------------------------------------------------------------------ *)
  let gen_rcond pf b m at_pos s =
    let head, i, tail = s_split_i at_pos s in
    let e, s =
      match i.i_node with
      | Sif(e,s1,s2) -> e, if b then s1.s_node else s2.s_node
      | Swhile(e,s1) -> e, if b then s1.s_node@[i] else []
      | _ ->
          tc_error_lazy pf (fun fmt ->
            Format.fprintf fmt
              "the %ith instruction is not a conditionnal" at_pos)
    in
    let e = form_of_expr m e in
    let e = if b then e else f_not e in

    (stmt head, e, stmt (head @ s @ tail))

  (* ------------------------------------------------------------------ *)
  let t_hoare_rcond_r b at_pos tc =
    let hs = tc1_as_hoareS tc in
    let m  = EcMemory.memory hs.hs_m in
    let hd,e,s = gen_rcond !!tc b m at_pos hs.hs_s in
    let concl1  = f_hoareS_r { hs with hs_s = hd; hs_po = e } in
    let concl2  = f_hoareS_r { hs with hs_s = s } in
    FApi.xmutate1 tc `RCond [concl1; concl2]

  (* ------------------------------------------------------------------ *)
  let t_bdhoare_rcond_r b at_pos tc =
    let bhs = tc1_as_bdhoareS tc in
    let m  = EcMemory.memory bhs.bhs_m in
    let hd,e,s = gen_rcond !!tc b m at_pos bhs.bhs_s in
    let concl1  = f_hoareS bhs.bhs_m bhs.bhs_pr hd e in
    let concl2  = f_bdHoareS_r { bhs with bhs_s = s } in
    FApi.xmutate1 tc `RCond [concl1; concl2]

  (* ------------------------------------------------------------------ *)
  let t_equiv_rcond_r side b at_pos tc =
    let es = tc1_as_equivS tc in
    let m,mo,s =
      match side with
      | `Left  -> es.es_ml,es.es_mr, es.es_sl
      | `Right -> es.es_mr,es.es_ml, es.es_sr in
    let hd,e,s = gen_rcond !!tc b EcFol.mhr at_pos s in
    let mo' = EcIdent.create "&m" in
    let s1 = Fsubst.f_subst_id in
    let s1 = Fsubst.f_bind_mem s1 (EcMemory.memory m) EcFol.mhr in
    let s1 = Fsubst.f_bind_mem s1 (EcMemory.memory mo) mo' in
    let pre1 = Fsubst.f_subst s1 es.es_pr in
    let concl1 =
      f_forall_mems [mo', EcMemory.memtype mo]
        (f_hoareS (EcFol.mhr, EcMemory.memtype m) pre1 hd e) in
    let sl,sr = match side with `Left -> s, es.es_sr | `Right -> es.es_sl, s in
    let concl2 = f_equivS_r { es with es_sl = sl; es_sr = sr } in
    FApi.xmutate1 tc `RCond [concl1; concl2]

  (* ------------------------------------------------------------------ *)
  let t_hoare_rcond   = FApi.t_low2 "hoare-rcond"   t_hoare_rcond_r
  let t_bdhoare_rcond = FApi.t_low2 "bdhoare-rcond" t_bdhoare_rcond_r
  let t_equiv_rcond   = FApi.t_low3 "equiv-rcond"   t_equiv_rcond_r
end

(* -------------------------------------------------------------------- *)
let t_rcond side b at_pos tc =
  let concl = FApi.tc1_goal tc in

  match side with
  | None when is_bdHoareS concl -> Low.t_bdhoare_rcond b at_pos tc
  | None -> Low.t_hoare_rcond b at_pos tc
  | Some side -> Low.t_equiv_rcond side b at_pos tc
