(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2014 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcModules
open EcFol
open EcParsetree

open EcCoreGoal
open EcLowPhlGoal

(*
 *   SP carries three elements,
 *   - bds: a set of existential binders
 *   - assoc: a set of pairs (x,e) such that x=e holds
 *            for instance after an assignment x <- e
 *   - pre: the actual precondition (progressively weakened)
 *   After an assignment of the form x <- e the three elements are updated.
 *   Normally,
 *   1) a new fresh local x' is added to the list of existential binders
 *   2) (x,e) is added to the assoc list, and every other (y,d) is replaced by
 *      (y[x->x'],d[x->x'])
 *   3) pre is replaced by pre[x->x']
 *  The simplification of this version comes from two tricks.
 *  First, notice that the replacement of (y[x->x']) introduces a simplification
 *  opportunity. There is no need to keep (x',d[x->x']) as a
 *  conjuction x'=d[x->x']: it is enough to perform the substitution
 *  of d[x->x'] for x' in place
 *  (it is a mess however to implement this idea with simultaneous assigns)
 *  The second ...
 *)

(* -------------------------------------------------------------------- *)
module LowInternal = struct
  (* ------------------------------------------------------------------ *)
  exception No_sp

  (* ------------------------------------------------------------------ *)
  type assignable =
  | APVar  of (EcTypes.prog_var * EcTypes.ty)
  | ALocal of (EcIdent.t * EcTypes.ty)

  type assoc_t = (assignable list * form) list

  (* ------------------------------------------------------------------ *)
  let isAPVar  = function APVar  _ -> true | _ -> false
  let isALocal = function ALocal _ -> true | _ -> false

  (* ------------------------------------------------------------------ *)
  let rec sp_asgn mem env lv e (bds,assoc,pre) =
    (* aux substitution function *)
    let subst_in_assoc lv new_id_exp new_ids ((ass:assignable list),f) =
      let replace_assignable var = match var with
        | APVar (pv',ty) ->
          begin
            match lv,new_ids with
              | LvVar(pv,_), [new_id,_] when EcTypes.pv_equal pv pv'
                  -> ALocal (new_id,ty)
              | LvVar _, _ -> var
              | LvTuple vs,_ ->
                begin
                  let aux = List.map2 (fun (pv,_) (new_id,_) -> pv,new_id) vs new_ids in
                  try
                    let new_id = snd (List.find (fun (pv,_) -> EcTypes.pv_equal pv pv') aux) in
                    ALocal (new_id,ty)
                  with Not_found -> var
                end
              | _ -> assert false (* bug *)
          end
        | _ -> var
      in
      let ass = List.map replace_assignable ass in
      let f = subst_form_lv env mem lv new_id_exp f in
      (ass,f)
    in
    (* aux simplification function *)
    let rec simplify_assoc (bds,assoc) = match assoc with
      | [] -> bds,[]
      | (ass,f) :: assoc ->
        let bds,assoc = simplify_assoc (bds,assoc) in
        let destr_ass =
          try List.combine (List.map (fun x -> [x]) ass) (destr_tuple f)
          with Invalid_argument _ | DestrError _ -> [(ass,f)]
        in
        let do_subst_or_accum (bds,assoc) (a,f) =
          match a with
          | [ALocal (id,_)] ->
            let subst = EcFol.Fsubst.f_subst_id in
            let subst = EcFol.Fsubst.f_bind_local subst id f in
            List.filter (fun (id',_) -> id'<>id) bds, List.map (fun (ass',f') ->
              (ass', EcFol.Fsubst.f_subst subst f')) assoc
          | _ -> bds,(a,f) :: assoc
        in
        let (bds,assoc) = List.fold_left do_subst_or_accum (bds,assoc) destr_ass in
        bds,assoc
    in
    match lv with
      | LvVar(pv,t_pv) ->
        let new_id = EcIdent.create (EcIdent.name (id_of_pv pv mem)) in
        let bds = (new_id,t_pv)::bds in
        let new_id_e = f_local new_id t_pv in
        let pre = subst_form_lv env mem lv new_id_e pre in
        let e_form = EcFol.form_of_expr mem e in
        let e_form = subst_form_lv env mem lv new_id_e e_form in
        let assoc = ([APVar (pv,t_pv)],e_form) ::
          List.map (subst_in_assoc lv new_id_e [new_id,t_pv]) assoc
        in
        let (bds,assoc) = simplify_assoc (bds,List.rev assoc) in
        let assoc = List.rev assoc in
        bds,assoc,pre
      | LvTuple vs ->
        let new_typed_ids = List.map
          (fun (pv,t)-> EcIdent.create (EcIdent.name (id_of_pv pv mem)),t) vs
        in
        let bds = new_typed_ids @ bds in
        let new_ids_tuple = f_tuple
          (List.map (fun (id,t) -> f_local id t) new_typed_ids) in
        let pre =
          subst_form_lv env mem lv new_ids_tuple pre
        in
        let e_form = EcFol.form_of_expr mem e in
        let e_form = subst_form_lv env mem lv new_ids_tuple e_form in
        let new_assoc = List.map (fun x -> APVar x) vs, e_form in
        let assoc = new_assoc::List.map
          (subst_in_assoc lv new_ids_tuple new_typed_ids) assoc in
        let (bds,assoc) = simplify_assoc (bds,List.rev assoc) in
        let assoc = List.rev assoc in
        bds,assoc,pre
      | LvMap((p,tys),pv,e',ty) ->
        let map_type = EcTypes.toarrow [ty;e'.EcTypes.e_ty;e.EcTypes.e_ty] ty in
        let set = EcTypes.e_op p tys map_type in
        let e = EcTypes.e_app set [EcTypes.e_var pv ty; e'; e] ty in
        sp_asgn mem env (LvVar(pv,ty)) e (bds,assoc,pre)

  (* ------------------------------------------------------------------ *)
  let build_sp mem bds assoc pre =
    let f_assoc a = match a with
      | APVar (pv,pv_ty) -> f_pvar pv pv_ty mem
      | ALocal (lv,lv_ty) -> f_local lv lv_ty
    in
    let rem_ex (assoc,f) (x_id,x_ty) =
      try
        let rec partition_on_x assoc = match assoc with
          | [] -> raise Not_found
          | (a,e) :: assoc when f_equal e (f_local x_id x_ty) ->
            a,assoc
          | x :: assoc ->
            let a,assoc = partition_on_x assoc in
            a,x::assoc
        in
        let a,assoc = partition_on_x assoc in
        let a = f_tuple (List.map f_assoc a) in
        let subst = EcFol.Fsubst.f_subst_id in
        let subst = EcFol.Fsubst.f_bind_local subst x_id a in
        let f = EcFol.Fsubst.f_subst subst f in
        let subst_in_assoc (ass,f) = (ass,EcFol.Fsubst.f_subst subst f)in
        let assoc = List.map subst_in_assoc assoc in
        assoc,f
      with Not_found -> (assoc,f)
    in
    let (assoc,pre) = List.fold_left rem_ex (assoc,pre) bds in
    let merge_assoc f (a,e) =
      let a = f_tuple (List.map f_assoc a) in
      f_and_simpl (f_eq_simpl a e) f
    in
    let pre = List.fold_left merge_assoc pre assoc in
    EcFol.f_exists_simpl (List.map (fun (id,t) -> (id,EcFol.GTty t)) bds) pre

  (* ------------------------------------------------------------------ *)
  let rec sp_stmt m env (bds,assoc,pre) stmt = match stmt with
    | [] -> [],(bds,assoc,pre)
    | i::is ->
      try
        let (bds,assoc,pre) = sp_instr m env (bds,assoc,pre) i in
        sp_stmt m env (bds,assoc,pre) is
      with No_sp ->
        stmt, (bds,assoc,pre)
  and sp_instr m env (bds,assoc,pre) instr = match instr.i_node with
    | Sasgn (lv,e) -> sp_asgn m env lv e (bds,assoc,pre)
    | Sif (e,s1,s2) ->
      let e_form = EcFol.form_of_expr m e in
      let pre_t = build_sp m bds assoc (f_and_simpl e_form pre) in
      let pre_f = build_sp m bds assoc (f_and_simpl (f_not e_form) pre) in
      let stmt_t,(bds_t,assoc_t,pre_t) = sp_stmt m env (bds,assoc,pre_t) s1.s_node in
      let stmt_f,(bds_f,assoc_f,pre_f) = sp_stmt m env (bds,assoc,pre_f) s2.s_node in
      if (stmt_t<>[] || stmt_f<>[]) then raise No_sp;
      let sp_t = build_sp m bds_t assoc_t pre_t in
      let sp_f = build_sp m bds_f assoc_f pre_f in
      ([],[],f_or_simpl sp_t sp_f)
    | _ -> raise No_sp

  let sp_stmt m env stmt f =
    let stmt,(bds,assoc,pre) = sp_stmt m env ([],[],f) stmt in
    let pre = build_sp m bds assoc pre in
    stmt, pre
end

(* -------------------------------------------------------------------- *)
let destr_single_pos pf pos = match pos with
  | Some (Single i) -> Some i
  | None -> None
  | _ -> tc_error pf "bad usage of position parameter"

let destr_double_pos pf pos = match pos with
  | Some (Double (i,j)) -> Some i, Some j
  | None -> None, None
  | _ -> tc_error pf "Bad usage of position parameter"

let s_split pos stmt =
  match pos with
  | None   -> (stmt.s_node, [])
  | Some i -> s_split i stmt

(* -------------------------------------------------------------------- *)
let t_sp_side pos tc =
  let env, _, concl = FApi.tc1_eflat tc in

  match concl.f_node with
    | FhoareS hs ->
      let pos = destr_single_pos !!tc pos in
      let stmt1,stmt2 = s_split pos hs.hs_s in
      let (stmt1,pre) = LowInternal.sp_stmt (EcMemory.memory hs.hs_m) env stmt1 hs.hs_pr in
      let subgoal = f_hoareS_r {hs with hs_s=EcModules.stmt (stmt1@stmt2); hs_pr=pre} in
      FApi.xmutate1 tc `Sp [subgoal]

    | FbdHoareS bhs ->
      let pos = destr_single_pos !!tc pos in
      let stmt1,stmt2 = s_split pos bhs.bhs_s in
      begin (* being carefull with the bound expression *)
        let write_set = EcPV.s_write env (EcModules.stmt stmt1) in
        let read_set  = EcPV.PV.fv env (EcMemory.memory bhs.bhs_m) bhs.bhs_bd in
        if not (EcPV.PV.indep env write_set read_set) then
          tc_error !!tc "the bound expression can be modified"
      end;
      let (stmt1,pre) = LowInternal.sp_stmt (EcMemory.memory bhs.bhs_m) env stmt1 bhs.bhs_pr in
      let subgoal = f_bdHoareS_r {bhs with bhs_s=EcModules.stmt (stmt1@stmt2); bhs_pr=pre} in
      FApi.xmutate1 tc `Sp [subgoal]

    | FequivS es ->
      let posL,posR = destr_double_pos !!tc pos in
      let stmtL1,stmtL2 = s_split posL es.es_sl in
      let stmtR1,stmtR2 = s_split posR es.es_sr in
      let (stmtL1,pre) = LowInternal.sp_stmt (EcMemory.memory es.es_ml) env stmtL1 es.es_pr in
      let (stmtR1,pre) = LowInternal.sp_stmt (EcMemory.memory es.es_mr) env stmtR1 pre in
      let subgoal = f_equivS_r {es with
        es_sl=EcModules.stmt (stmtL1@stmtL2);
        es_sr=EcModules.stmt (stmtR1@stmtR2);
        es_pr=pre
      } in
      FApi.xmutate1 tc `Sp [subgoal]

    | _ -> tc_error !!tc "expects a statement judgment as goal"

(* -------------------------------------------------------------------- *)
let t_sp = FApi.t_low1 "sp" t_sp_side
