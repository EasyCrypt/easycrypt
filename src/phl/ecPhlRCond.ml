(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcTypes
open EcDecl
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
              "the targetted instruction is not a conditionnal")
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

(* -------------------------------------------------------------------- *)
module LowMatch = struct
  (* ------------------------------------------------------------------ *)
  let gen_rcond (pf, env) c m at_pos s =
    let head, i, tail = s_split_i at_pos s in
    let e, (cname, cty), (cvars, subs) =
      match i.i_node with
      | Smatch (e, bs) -> begin
          let typ, tyd, _ = oget (EcEnv.Ty.get_top_decl e.e_ty env) in
          let tyd = oget (EcDecl.tydecl_as_datatype tyd) in
          let ctor =
            let test (_i : int) = sym_equal c -| fst in
            List.Exceptionless.findi test tyd.tydt_ctors in

          match ctor with
          | None ->
              tc_error_lazy pf (fun fmt ->
                  Format.fprintf fmt
                    "cannot find the constructor %s" c)

          | Some (i, (cname, cty)) ->
              let b = oget (List.nth_opt bs i) in
              let cname = EcPath.pqoname (EcPath.prefix typ) cname in
              (e, (cname, cty), b)
        end

      | _ ->
          tc_error_lazy pf (fun fmt ->
            Format.fprintf fmt
              "the targetted instruction is not a match")
    in

    let e = form_of_expr m e in

    (stmt head, e, stmt (head @ subs.s_node @ tail))

  (* ------------------------------------------------------------------ *)
  let t_hoare_rcond_match_r c at_pos tc =
    let hs = tc1_as_hoareS tc in
    let m  = EcMemory.memory hs.hs_m in
    let hd, _e, s = gen_rcond (!!tc, FApi.tc1_env tc) c m at_pos hs.hs_s in
    let concl1  = f_hoareS_r { hs with hs_s = hd; hs_po = f_true; } in
    let concl2  = f_hoareS_r { hs with hs_s = s; } in
    FApi.xmutate1 tc `RCondMatch [concl1; concl2]

  (* ------------------------------------------------------------------ *)
  let t_bdhoare_rcond_match_r c at_pos tc =
    EcLowGoal.t_id tc

  (* ------------------------------------------------------------------ *)
  let t_equiv_rcond_match_r side c at_pos tc =
    EcLowGoal.t_id tc

  (* ------------------------------------------------------------------ *)
  let t_hoare_rcond_match =
    FApi.t_low2 "hoare-rcond-match" t_hoare_rcond_match_r

  let t_bdhoare_rcond_match =
    FApi.t_low2 "hoare-rcond-match" t_bdhoare_rcond_match_r

  let t_equiv_rcond_match =
    FApi.t_low3 "hoare-rcond-match" t_equiv_rcond_match_r
end

(* -------------------------------------------------------------------- *)
let t_rcond_match side c at_pos tc =
  let concl = FApi.tc1_goal tc in

  match side with
  | None when is_bdHoareS concl -> LowMatch.t_bdhoare_rcond_match c at_pos tc
  | None -> LowMatch.t_hoare_rcond_match c at_pos tc
  | Some side -> LowMatch.t_equiv_rcond_match side c at_pos tc
