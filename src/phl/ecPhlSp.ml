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
open EcParsetree
open EcEnv
open EcCoreGoal
open EcLowPhlGoal

(*
 * SP carries three elements,
 *   - bds: a set of existential binders
 *   - assoc: a set of pairs (x,e) such that x=e holds
 *            for instance after an assignment x <- e
 *   - pre: the actual precondition (progressively weakened)
 *
 * After an assignment of the form x <- e the three elements are updated:
 *   1) a new fresh local x' is added to the list of existential binders
 *   2) (x, e) is added to the assoc list, and every other (y,d) is replaced
 *      by (y[x->x'], d[x->x'])
 *   3) pre is replaced by pre[x->x']
 *
 *  The simplification of this version comes from two tricks:
 *
 *   1) the replacement of (y[x->x']) introduces a simplification
 *      opportunity. There is no need to keep (x', d[x->x']) as a
 *      conjuction x' = d[x->x']: it is enough to perform the substitution
 *      of d[x->x'] for x' in place (it is a mess however to implement this
 *      idea with simultaneous assigns)
 *   2) $MISSING...
 *)

(* -------------------------------------------------------------------- *)
module LowInternal = struct
  (* ------------------------------------------------------------------ *)
  exception No_sp

  (* ------------------------------------------------------------------ *)
  type assignable =
  | APVar  of (prog_var  * ty)
  | ALocal of (EcIdent.t * ty)

  and assignables = assignable list

  type assoc_t = (assignable list * form) list

  (* ------------------------------------------------------------------ *)
  let isAPVar  = function APVar  _ -> true | _ -> false
  let isALocal = function ALocal _ -> true | _ -> false

  (* ------------------------------------------------------------------ *)
  let rec sp_asgn mem env lv e (bds, assoc, pre) =
    let subst_in_assoc lv new_id_exp new_ids ((ass : assignables), f) =
      let replace_assignable var =
        match var with
        | APVar (pv', ty) ->  begin
          match lv,new_ids with
          | LvVar (pv ,_), [new_id,_] when NormMp.pv_equal env pv pv' ->
              ALocal (new_id,ty)

          | LvVar _, _ ->
              var

          | LvTuple vs, _ -> begin
              let aux = List.map2 (fun x y -> (fst x, fst y)) vs new_ids in
              try
                let new_id = snd (List.find (NormMp.pv_equal env pv' |- fst) aux) in
                ALocal (new_id, ty)
              with Not_found -> var
            end
        end
        | _ -> var

      in let ass = List.map replace_assignable ass in
         let f   = subst_form_lv env mem lv new_id_exp f in
         (ass, f)
    in

    let rec simplify_assoc (assoc, bds, pre) =
      match assoc with
      | [] ->
          ([], bds, pre)

      | (ass, f) :: assoc ->
          let assoc, bds, pre = simplify_assoc (assoc, bds, pre) in

          let destr_ass =
            try  List.combine (List.map in_seq1 ass) (destr_tuple f)
            with Invalid_argument _ | DestrError _ -> [(ass, f)]
          in

          let do_subst_or_accum (assoc, bds, pre) (a, f) =
          match a with
          | [ALocal (id, _)] ->
              let subst = EcFol.Fsubst.f_subst_id in
              let subst = EcFol.Fsubst.f_bind_local subst id f in
              (List.map (snd_map (EcFol.Fsubst.f_subst subst)) assoc,
               List.filter ((<>) id |- fst) bds,
               EcFol.Fsubst.f_subst subst pre)

          | _ -> ((a, f) :: assoc, bds, pre)
        in
        List.fold_left do_subst_or_accum (assoc, bds, pre) destr_ass
    in

    let for_lvars vs =
        let fresh pv = EcIdent.create (EcIdent.name (id_of_pv pv mem)) in

        let newids  = List.map (fst_map fresh) vs in
        let bds     = newids @ bds in
        let astuple = f_tuple (List.map (curry f_local) newids) in
        let pre     = subst_form_lv env mem lv astuple pre in
        let e_form  = EcFol.form_of_expr mem e in
        let e_form  = subst_form_lv env mem lv astuple e_form in

        let assoc =
             (List.map (fun x -> APVar x) vs, e_form)
          :: (List.map (subst_in_assoc lv astuple newids) assoc) in

        let assoc, bds, pre = simplify_assoc (List.rev assoc, bds, pre) in

        (bds, List.rev assoc, pre)
    in

    match lv with
    | LvVar   v  -> for_lvars [v]
    | LvTuple vs -> for_lvars vs

  (* ------------------------------------------------------------------ *)
  let build_sp mem bds assoc pre =
    let f_assoc = function
      | APVar  (pv, pv_ty) -> f_pvar pv pv_ty mem
      | ALocal (lv, lv_ty) -> f_local lv lv_ty
    in

    let rem_ex (assoc, f) (x_id, x_ty) =
      try
        let rec partition_on_x = function
          | [] ->
              raise Not_found
          | (a, e) :: assoc when f_equal e (f_local x_id x_ty) ->
              (a, assoc)
          | x :: assoc ->
              let a, assoc = partition_on_x assoc in (a, x::assoc)
        in
        let a,assoc = partition_on_x assoc in
        let a       = f_tuple (List.map f_assoc a) in
        let subst   = EcFol.Fsubst.f_subst_id in
        let subst   = EcFol.Fsubst.f_bind_local subst x_id a in
        let f       = EcFol.Fsubst.f_subst subst f in
        let assoc   = List.map (snd_map (EcFol.Fsubst.f_subst subst)) assoc in
        (assoc, f)

      with Not_found -> (assoc, f)
    in

    let assoc, pre = List.fold_left rem_ex (assoc, pre) bds in
    let pre =
      let merge_assoc f (a, e) =
        f_and_simpl (f_eq_simpl (f_tuple (List.map f_assoc a)) e) f
      in List.fold_left merge_assoc pre assoc in

    EcFol.f_exists_simpl (List.map (snd_map (fun t -> GTty t)) bds) pre

  (* ------------------------------------------------------------------ *)
  let rec sp_stmt m env (bds, assoc, pre) stmt =
    match stmt with
    | [] ->
        ([], (bds, assoc, pre))

    | i :: is ->
        try
          let (bds, assoc, pre) = sp_instr m env (bds, assoc, pre) i in
          sp_stmt m env (bds,assoc,pre) is
        with No_sp ->
          (stmt, (bds, assoc, pre))

  and sp_instr m env (bds,assoc,pre) instr = match instr.i_node with
    | Sasgn (lv, e) ->
        sp_asgn m env lv e (bds, assoc, pre)

    | Sif (e, s1, s2) ->
        let e_form = EcFol.form_of_expr m e in
        let pre_t  = build_sp m bds assoc (f_and_simpl e_form pre) in
        let pre_f  = build_sp m bds assoc (f_and_simpl (f_not e_form) pre) in
        let stmt_t, (bds_t, assoc_t, pre_t) = sp_stmt m env (bds, assoc, pre_t) s1.s_node in
        let stmt_f, (bds_f, assoc_f, pre_f) = sp_stmt m env (bds, assoc, pre_f) s2.s_node in
        if not (List.is_empty stmt_t && List.is_empty stmt_f) then raise No_sp;
        let sp_t = build_sp m bds_t assoc_t pre_t in
        let sp_f = build_sp m bds_f assoc_f pre_f in
        ([], [], f_or_simpl sp_t sp_f)

    | _ -> raise No_sp

  let sp_stmt m env stmt f =
    let stmt, (bds, assoc, pre) = sp_stmt m env ([], [], f) stmt in
    let pre = build_sp m bds assoc pre in
    stmt, pre
end

(* -------------------------------------------------------------------- *)
let t_sp_side pos tc =
  let module LI = LowInternal in

  let env, _, concl = FApi.tc1_eflat tc in

  let as_single = function Single i -> i | _ -> assert false
  and as_double = function Double i -> i | _ -> assert false in

  let check_sp_progress ?side pos stmt =
    if is_some pos && not (List.is_empty stmt) then
      tc_error_lazy !!tc (fun fmt ->
        let side = side |> (function
          | None          -> "remaining"
          | Some (`Left ) -> "remaining on the left"
          | Some (`Right) -> "remaining on the right")
        in

        Format.fprintf fmt
          "%d instruction(s) %s, change your [sp] bound"
          (List.length stmt) side)
  in

  match concl.f_node, pos with
  | FhoareS hs, (None | Some (Single _)) ->
      let pos = pos |> omap as_single in
      let stmt1, stmt2 = o_split ~rev:true pos hs.hs_s in
      let stmt1, hs_pr = LI.sp_stmt (EcMemory.memory hs.hs_m) env stmt1 hs.hs_pr in
      check_sp_progress pos stmt1;
      let subgoal = f_hoareS_r { hs with hs_s = stmt (stmt1@stmt2); hs_pr } in
      FApi.xmutate1 tc `Sp [subgoal]

  | FbdHoareS bhs, (None | Some (Single _)) ->
      let pos = pos |> omap as_single in
      let stmt1, stmt2 = o_split ~rev:true pos bhs.bhs_s in
      begin
        let write_set = EcPV.s_write env (EcModules.stmt stmt1) in
        let read_set  = EcPV.PV.fv env (EcMemory.memory bhs.bhs_m) bhs.bhs_bd in
        if not (EcPV.PV.indep env write_set read_set) then
          tc_error !!tc "the bound should not be modified by the statement targeted by [sp]"
      end;
      let stmt1, bhs_pr = LI.sp_stmt (EcMemory.memory bhs.bhs_m) env stmt1 bhs.bhs_pr in
      check_sp_progress pos stmt1;
      let subgoal = f_bdHoareS_r {bhs with bhs_s = stmt (stmt1@stmt2); bhs_pr; } in
      FApi.xmutate1 tc `Sp [subgoal]

  | FequivS es, (None | Some (Double _))  ->
      let pos  = pos |> omap as_double in
      let posL = pos |> omap fst in
      let posR = pos |> omap snd in

      let stmtL1, stmtL2 = o_split ~rev:true posL es.es_sl in
      let stmtR1, stmtR2 = o_split ~rev:true posR es.es_sr in

      let         es_pr = es.es_pr in
      let stmtL1, es_pr = LI.sp_stmt (EcMemory.memory es.es_ml) env stmtL1 es_pr in
      let stmtR1, es_pr = LI.sp_stmt (EcMemory.memory es.es_mr) env stmtR1 es_pr in

      check_sp_progress ~side:`Left  pos stmtL1;
      check_sp_progress ~side:`Right pos stmtR1;

      let subgoal = f_equivS_r { es with
        es_sl = stmt (stmtL1@stmtL2);
        es_sr = stmt (stmtR1@stmtR2);
        es_pr =es_pr;
      } in

      FApi.xmutate1 tc `Sp [subgoal]

  | _, Some (Single _) -> tc_error_noXhl ~kinds:[`Hoare `Stmt; `PHoare `Stmt] !!tc
  | _, Some (Double _) -> tc_error_noXhl ~kinds:[`Equiv `Stmt] !!tc
  | _, None            -> tc_error_noXhl ~kinds:(hlkinds_Xhl_r `Stmt) !!tc

(* -------------------------------------------------------------------- *)
let t_sp = FApi.t_low1 "sp" t_sp_side
