(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcTypes
open EcModules
open EcFol
open EcEnv
open EcPV

open EcCoreGoal
open EcLowPhlGoal

module Mid = EcIdent.Mid
module Zpr = EcMatching.Zipper
module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
let t_kill_r side cpos olen tc =
  let env = FApi.tc1_env tc in

  let kill_stmt (pf, _) (_, po) me zpr =
    let (ks, tl) =
      match olen with
      | None -> (zpr.Zpr.z_tail, [])
      | Some len ->
          if List.length zpr.Zpr.z_tail < len then
            tc_error pf
              "cannot find %d consecutive instructions at given position"
              len;
          List.takedrop len zpr.Zpr.z_tail
    in

    (* FIXME [BG]: check the usage of po_rd *)
    let ks_wr = is_write env ks in
    let po_rd = PV.fv env (fst me) po in

    let pp_of_name =
      let ppe = EcPrinting.PPEnv.ofenv env in
        fun fmt x ->
          match x with
          | `Global p -> EcPrinting.pp_topmod ppe fmt p
          | `PV     p -> EcPrinting.pp_pv     ppe fmt p
    in

    List.iteri
      (fun i is ->
         let is_rd = is_read env is in
         let indp  = PV.interdep env ks_wr is_rd in
           match PV.pick indp with
           | None   -> ()
           | Some x ->
               match i with
               | 0 ->
                   tc_error !!tc
                     "code writes variables (%a) used by the current block"
                     pp_of_name x
               | _ ->
                   tc_error !!tc
                     "code writes variables (%a) used by the %dth parent block"
                     pp_of_name x i)
      (Zpr.after ~strict:false { zpr with Zpr.z_tail = tl; });

    begin
      match PV.pick (PV.interdep env ks_wr po_rd) with
      | None   -> ()
      | Some x ->
          tc_error !!tc
            "code writes variables (%a) used by the post-condition"
            pp_of_name x
    end;

    let kslconcl = EcFol.f_bdHoareS me f_true (stmt ks) f_true FHeq f_r1 in
      (me, { zpr with Zpr.z_tail = tl; }, [kslconcl])
  in

  let tr = fun side -> `Kill (side, cpos, olen) in
  t_code_transform side ~bdhoare:true cpos tr (t_zip kill_stmt) tc

(* -------------------------------------------------------------------- *)
let alias_stmt env id (pf, _) me i =
  let dopv ty =
    let id       = odfl "x" (omap EcLocation.unloc id) in
    let id       = { v_name = id; v_type = ty; } in
    let (me, id) = fresh_pv me id in
    let pv       = pv_loc (EcMemory.xpath me) id in
    me, pv in

  match i.i_node with
  | Sasgn(lv,e) ->
    let ty = e.e_ty in
    let (me, pv) = dopv ty in
    (me, [i_asgn (LvVar (pv, ty), e); i_asgn (lv, e_var pv ty)])
  | Srnd (lv, e) ->
    let ty       = proj_distr_ty env e.e_ty in
    let (me, pv) = dopv ty in
    (me, [i_rnd (LvVar (pv, ty), e); i_asgn (lv, e_var pv ty)])
  | Scall (Some lv, f, args) ->
    let ty       = (EcEnv.Fun.by_xpath f env).f_sig.fs_ret in
    let (me, pv) = dopv ty in
    (me, [i_call (Some (LvVar (pv, ty)), f ,args); i_asgn (lv, e_var pv ty)])
  | _ ->
      tc_error pf "cannot create an alias for that kind of instruction"

let t_alias_r side cpos id g =
  let env = FApi.tc1_env g in
  let tr = fun side -> `Alias (side, cpos) in
  t_code_transform side ~bdhoare:true cpos tr (t_fold (alias_stmt env id)) g

(* -------------------------------------------------------------------- *)
let set_stmt (fresh, id) e =
  let get_i me =
    let id       = EcLocation.unloc id in
    let  v       = { v_name = id; v_type = e.e_ty } in
    let (me, id) = fresh_pv me v in
    let pv       = pv_loc (EcMemory.xpath me) id in

    (me, i_asgn (LvVar (pv, e.e_ty), e))
  in

  let get_i =
    if fresh then get_i
    else
      let res = ref None in
      fun me ->
        if !res = None then res := Some (get_i me);
        oget !res in
  fun _ _ me z ->
    let me,i = get_i me in
    (me, {z with Zpr.z_tail = i::z.Zpr.z_tail},[])

let t_set_r side cpos (fresh, id) e tc =
  let tr = fun side -> `Set (side, cpos) in
  t_code_transform side ~bdhoare:true cpos tr (t_zip (set_stmt (fresh, id) e)) tc

(* -------------------------------------------------------------------- *)
let cfold_stmt (pf, hyps) me olen zpr =
  let env = LDecl.toenv hyps in

  let (asgn, i, tl) =
    match zpr.Zpr.z_tail with
    | ({ i_node = Sasgn (lv, e) } as i) :: tl -> begin
      let asgn =
        match lv with
        | LvVar (x, ty) -> [(x, ty, e)]
        | LvTuple xs -> begin
            match e.e_node with
            | Etuple es -> List.map2 (fun (x, ty) e -> (x, ty, e)) xs es
            | _ -> assert false
        end
      in
        (asgn, i, tl)
    end

    | _ ->
        tc_error pf "cannot find a left-value assignment at given position"
  in

  let (tl1, tl2) =
    match olen with
    | None      -> (tl, [])
    | Some olen ->
        if List.length tl < olen then
          tc_error pf "expecting at least %d instructions after assignment" olen;
        List.takedrop olen tl
  in

  List.iter
    (fun (x, _, _) ->
      if x.pv_kind <> PVloc then
        tc_error pf "left-values must be local variables")
    asgn;

  List.iter
    (fun (_, _, e) ->
        if e_fv e <> Mid.empty || e_read env e <> PV.empty then
          tc_error pf "right-values are not closed expression")
    asgn;

  let wrs = is_write env tl1 in
  let asg = List.fold_left
              (fun pv (x, ty, _) -> EcPV.PV.add env x ty pv)
              EcPV.PV.empty asgn
  in

  if not (EcPV.PV.indep env wrs asg) then
    tc_error pf "cannot cfold non read-only local variables";

  let subst =
    List.fold_left
      (fun subst (x, _ty, e) ->  Mpv.add env x e subst)
      Mpv.empty asgn
  in

  let tl1 = Mpv.issubst env subst tl1 in

  let zpr =
    { zpr with Zpr.z_tail = tl1 @ (i :: tl2) }
  in
    (me, zpr, [])

let t_cfold_r side cpos olen g =
  let tr = fun side -> `Fold (side, cpos, olen) in
  let cb = fun cenv _ me zpr -> cfold_stmt cenv me olen zpr in
  t_code_transform side ~bdhoare:true cpos tr (t_zip cb) g

(* -------------------------------------------------------------------- *)
let t_kill  = FApi.t_low3 "code-tx-kill"  t_kill_r
let t_alias = FApi.t_low3 "code-tx-alias" t_alias_r
let t_set   = FApi.t_low4 "code-tx-set"   t_set_r
let t_cfold = FApi.t_low3 "code-tx-cfold" t_cfold_r

(* -------------------------------------------------------------------- *)
let process_cfold (side, cpos, olen) tc =
  t_cfold side cpos olen tc

let process_kill (side, cpos, len) tc =
  t_kill side cpos len tc

let process_alias (side, cpos, id) tc =
  t_alias side cpos id tc

let process_set (side, cpos, fresh, id, e) tc =
  let e = TTC.tc1_process_Xhl_exp tc side None e in
  t_set side cpos (fresh, id) e tc
