(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcAst
open EcTypes
open EcModules
open EcFol

open EcPlTransform

(* -------------------------------------------------------------------- *)
(* The instruction at the resolved index [k] of [s], with the prefix (in
   order) and the suffix. *)
let split_at (k : EcMatching.Position.nm_codepos1) (s : stmt) =
  try  EcMatching.Position.find_by_nmcpos1 ~rev:false k s
  with EcMatching.Position.InvalidCPos ->
    raise (InvalidTransform "invalid instruction index")

(* -------------------------------------------------------------------- *)
let rcond_select (m : memory) k (b : bool) (s : stmt) =
  let hd, i, tl = split_at k s in
  let e, s =
    match i.i_node with
    | Sif (e, s1, s2) -> e, if b then s1.s_node else s2.s_node
    | Swhile (e, s1)  -> e, if b then s1.s_node @ [i] else []
    | _ -> raise (InvalidTransform "the targetted instruction is not a conditionnal") in
  let g = ss_inv_of_expr m e in
  let g = if b then g else map_ss_inv1 f_not g in
  (stmt hd, g, stmt (hd @ s @ tl))

(* -------------------------------------------------------------------- *)
type rmatch = {
  rm_hd       : stmt;
  rm_post     : ss_inv;
  rm_me       : memenv;
  rm_eq       : ss_inv;
  rm_framed   : stmt;
  rm_unframed : stmt;
}

let rmatch_select (env : EcEnv.env) (me0 : memenv) k (j : int) (s : stmt) =
  let m = EcMemory.memory me0 in
  let hd, i, tl = split_at k s in
  let e, bs =
    match i.i_node with
    | Smatch (e, bs) -> e, bs
    | _ -> raise (InvalidTransform "the targetted instruction is not a match") in
  let typ, tydc, tyinst = oget (EcEnv.Ty.get_top_decl e.e_ty env) in
  let tyd = oget (EcDecl.tydecl_as_datatype tydc) in
  let (cname, _), (cvars, b) =
    try  List.nth tyd.tydt_ctors j, List.nth bs j
    with Invalid_argument _ | Failure _ ->
      raise (InvalidTransform "invalid constructor index") in
  let cname  = EcPath.pqoname (EcPath.prefix typ) cname in
  let tyinst = List.combine tydc.tyd_params tyinst in
  let f = ss_inv_of_expr m e in

  (* exists xs, e = C xs *)
  let post =
    let names = List.map (
      fun (x, xty) ->
        let x =
          if   EcIdent.name x = "_"
          then EcIdent.create (symbol_of_ty xty)
          else EcIdent.fresh x
        in (x, xty)) cvars in
    let vars = List.map (curry f_local) names in
    let cty = toarrow (List.snd names) f.inv.f_ty in
    let po = f_op cname (List.snd tyinst) cty in
    let po = f_app po vars f.inv.f_ty in
    map_ss_inv1 (f_exists (List.map (snd_map gtty) names)) (map_ss_inv2 f_eq f {m;inv=po}) in

  (* The arguments [xs] of [C] become fresh program variables [ys]. *)
  let me, pvs =
    let cvars =
      List.map
        (fun (x, xty) -> { ov_name = Some (EcIdent.name x); ov_type = xty; })
        cvars in
    EcMemory.bindall_fresh cvars me0 in

  let subst, pvs =
    List.fold_left_map (fun s ((x, xty), name) ->
        let pv = pv_loc (oget name.ov_name) in
        let s  = bind_elocal s x (e_var pv xty) in
        (s, (pv, xty)))
      Fsubst.f_subst_id (List.combine cvars pvs) in

  let b = (s_subst subst b).s_node in

  (* Framed form: e = C ys *)
  let eq =
    let vars = List.map (fun (pv, ty) -> f_pvar pv ty (fst me)) pvs in
    let epr = f_op cname (List.snd tyinst) f.inv.f_ty in
    let epr = map_ss_inv ~m:f.m (fun vars -> f_app epr vars f.inv.f_ty) vars in
    map_ss_inv2 f_eq f epr in

  (* Unframed form: ys <- oget (get_as_C e) *)
  let asgn =
    EcModules.lv_of_list pvs |> omap (fun lv ->
      let rty  = ttuple (List.snd cvars) in
      let proj = EcInductive.datatype_proj_path typ (EcPath.basename cname) in
      let proj = e_op proj (List.snd tyinst) (tfun e.e_ty (toption rty)) in
      let proj = e_app proj [e] (toption rty) in
      let proj = e_oget proj rty in
      i_asgn (lv, proj)) in

  { rm_hd       = stmt hd;
    rm_post     = post;
    rm_me       = me;
    rm_eq       = eq;
    rm_framed   = stmt (hd @ b @ tl);
    rm_unframed = stmt (hd @ otolist asgn @ b @ tl); }

(* -------------------------------------------------------------------- *)
let rmatch_can_frame (env : EcEnv.env) ~(can_frame : bool) k (s : stmt) =
  match split_at k s with
  | hd, { i_node = Smatch (e, _); _ }, _ ->
      let hd = stmt hd in
         (can_frame || List.is_empty hd.s_node)
      && EcPV.PV.indep env
           (EcPV.e_read env e)
           (EcPV.PV.union (EcPV.s_read env hd) (EcPV.s_write env hd))
  | _ -> false
  | exception InvalidTransform _ -> false

(* -------------------------------------------------------------------- *)
let resolve_at (env : EcEnv.env) (at : EcMatching.Position.codepos1) (s : stmt) =
  let module Pos = EcMatching.Position in
  try
    let k = Pos.normalize_cpos1 env at s in
    let _, i, _ = Pos.find_by_nmcpos1 ~rev:false k s in
    (k, i)
  with Pos.InvalidCPos -> raise (EcLowPhlGoal.InvalidSplit (`Instr at))

let resolve_rcond pe env at s =
  let k, i = resolve_at env at s in
  match i.i_node with
  | Sif _ | Swhile _ -> k
  | _ ->
      EcCoreGoal.tc_error_lazy pe (fun fmt ->
        Format.fprintf fmt "the targetted instruction is not a conditionnal")

let resolve_rmatch pe env at (c : symbol) s =
  let k, i = resolve_at env at s in
  match i.i_node with
  | Smatch (e, _) -> begin
      let _, tydc, _ = oget (EcEnv.Ty.get_top_decl e.e_ty env) in
      let tyd = oget (EcDecl.tydecl_as_datatype tydc) in
      match List.Exceptionless.findi (fun _ -> sym_equal c -| fst) tyd.tydt_ctors with
      | Some (j, _) -> (k, j)
      | None ->
          EcCoreGoal.tc_error_lazy pe (fun fmt ->
            Format.fprintf fmt "cannot find the constructor %s" c)
    end
  | _ ->
      EcCoreGoal.tc_error_lazy pe (fun fmt ->
        Format.fprintf fmt "the targetted instruction is not a match")
